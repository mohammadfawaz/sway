use crate::asm_generation::DataSection;
use crate::asm_lang::{virtual_register::*, RealizedOp, VirtualOp};
use petgraph::graph::{Graph, NodeIndex};
use std::collections::{BTreeSet, HashMap};

pub(crate) fn generate_liveness_tables(
    ops: &[RealizedOp],
    data_section: &DataSection,
) -> HashMap<usize, BTreeSet<VirtualRegister>> {
    let mut live_in: HashMap<usize, BTreeSet<VirtualRegister>> = HashMap::new();
    let mut live_out: HashMap<usize, BTreeSet<VirtualRegister>> = HashMap::new();

    for i in 0..ops.len() {
        live_in.insert(i, BTreeSet::new());
        live_out.insert(i, BTreeSet::new());
    }

    let mut inst_index: HashMap<usize, usize> = HashMap::new();
    let mut vec_index = 0;
    let mut actual_index = 0;
    for op in ops {
        if let VirtualOp::DataSectionOffsetPlaceholder = op.opcode {
            inst_index.insert(actual_index, vec_index);
            vec_index += 1;
            actual_index += 2;
        } else if let VirtualOp::LWDataId(_, ref data_id) = op.opcode {
            inst_index.insert(actual_index, vec_index);
            let type_of_data = data_section.type_of_data(data_id).expect(
            "Internal miscalculation in data section -- data id did not match up to any actual data",);
            if type_of_data.stack_size_of() > 1 {
                vec_index += 1;
                actual_index += 2;
            } else {
                vec_index += 1;
                actual_index += 1;
            }
        } else {
            inst_index.insert(actual_index, vec_index);
            vec_index += 1;
            actual_index += 1;
        }
    }

    let len = ops.len();
    let mut modified: bool;
    while {
        modified = false;
        //        for (index, op) in ops.iter().rev().enumerate() {
        for index in 0..ops.len() {
            let rev_index = len - index - 1;

            let mut op_use_filtered = ops[rev_index].opcode.use_registers();
            op_use_filtered.retain(|&x| matches!(x, VirtualRegister::Virtual(_)));

            let mut op_def_filtered = ops[rev_index].opcode.def_registers();
            op_def_filtered.retain(|&x| matches!(x, VirtualRegister::Virtual(_)));

            // Compute LIVE_out(op) = LIVE_in(s1) UNION LIVE_in(s2) UNION ... where s1, s2, ... are
            // successors of op
            let previous_live_out_for_op = live_out.get_mut(&rev_index).unwrap().clone();

            for s in &ops[rev_index]
                .opcode
                .successors(rev_index, ops, &inst_index)
            {
                let live_in_s = live_in.get(s).unwrap().clone();
                for l in &live_in_s {
                    live_out.get_mut(&rev_index).unwrap().insert(l.clone());
                }
            }
            if previous_live_out_for_op != live_out.get_mut(&rev_index).unwrap().clone() {
                modified = true;
            }

            // Compute LIVE_in(op) = use(op) UNION (LIVE_out(op) - def(op))
            // Add use(op)
            let previous_live_in_for_op = live_in.get_mut(&rev_index).unwrap().clone();
            for u in op_use_filtered {
                live_in.get_mut(&rev_index).unwrap().insert(u.clone());
            }

            // Add LIVE_out(op) - def(op)
            let mut live_out_minus_defs = live_out.get(&rev_index).unwrap().clone();
            for d in &op_def_filtered {
                live_out_minus_defs.remove(d);
            }

            for l in &live_out_minus_defs {
                live_in.get_mut(&rev_index).unwrap().insert(l.clone());
            }
            if previous_live_in_for_op != live_in.get_mut(&rev_index).unwrap().clone() {
                modified = true;
            }
        }
        modified
    } {}
    live_out
}

pub(crate) fn create_interference_graph(
    ops: &[RealizedOp],
    live_out: &HashMap<usize, BTreeSet<VirtualRegister>>,
) -> (
    Graph<VirtualRegister, (), petgraph::Undirected>,
    HashMap<VirtualRegister, NodeIndex>,
) {
    let mut interference_graph =
        Graph::<VirtualRegister, (), petgraph::Undirected>::new_undirected();

    let all_regs = ops.iter().fold(BTreeSet::new(), |mut tree, elem| {
        let mut regs = elem.opcode.registers();
        regs.retain(|&x| matches!(x, VirtualRegister::Virtual(_)));
        tree.extend(regs.into_iter());
        tree
    });

    let mut reg_to_node: HashMap<VirtualRegister, NodeIndex> = HashMap::new();

    for reg in all_regs {
        let node_idx = interference_graph.add_node(reg.clone());
        reg_to_node.insert(reg.clone(), node_idx);
    }

    for (idx, regs) in live_out {
        match &ops[*idx].opcode {
            VirtualOp::MOVE(a, c) => {
                if let Some(node_idx1) = reg_to_node.get(a) {
                    for b in regs.iter() {
                        if let Some(node_idx2) = reg_to_node.get(b) {
                            if *b != *c
                                && *b != *a
                                && !interference_graph.contains_edge(*node_idx1, *node_idx2)
                            {
                                interference_graph.add_edge(*node_idx1, *node_idx2, ());
                            }
                        }
                    }
                }
            }
            _ => {
                for a in &ops[*idx].opcode.def_registers() {
                    if let Some(node_idx1) = reg_to_node.get(a) {
                        for b in regs.iter() {
                            if let Some(node_idx2) = reg_to_node.get(b) {
                                if *b != **a
                                    && !interference_graph.contains_edge(*node_idx1, *node_idx2)
                                {
                                    interference_graph.add_edge(*node_idx1, *node_idx2, ());
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    (interference_graph, reg_to_node)
}

pub(crate) fn coalesce_registers(
    ops: &mut Vec<RealizedOp>,
    interference_graph: &mut Graph<VirtualRegister, (), petgraph::Undirected>,
    reg_to_node: &mut HashMap<VirtualRegister, NodeIndex>,
    data_section: &DataSection,
) -> Vec<RealizedOp> {
    let mut buf: Vec<RealizedOp> = vec![];
    let mut old_to_new_reg: HashMap<VirtualRegister, VirtualRegister> = HashMap::new();
    let mut full_map: HashMap<VirtualRegister, VirtualRegister> = HashMap::new();
    let mut inst_index: HashMap<usize, usize> = HashMap::new();
    let mut new_index: usize = 0;
    let mut old_index: usize = 0;
    for i in 0..ops.len() {
        if let VirtualOp::MOVE(r1, r2) = &ops[i].opcode {
            if let Some(idx1) = reg_to_node.get(r1) {
                if let Some(idx2) = reg_to_node.get(r2) {
                    if r1 == r2 {
                        inst_index.insert(old_index, new_index);
                        old_index += 1;
                        new_index += 1;
                        continue;
                    }
                    let move_is_needed = interference_graph.contains_edge(*idx1, *idx2);

                    if move_is_needed {
                        buf.push(ops[i].clone());
                        inst_index.insert(old_index, new_index);
                        old_index += 1;
                        new_index += 1;
                    } else {
                        let neighbors = interference_graph.neighbors(*idx1).collect::<Vec<_>>();
                        for neighbor in neighbors.clone() {
                            if !interference_graph.contains_edge(neighbor, *idx2) {
                                interference_graph.add_edge(neighbor, *idx2, ());
                            }
                        }
                        interference_graph.remove_node(*idx1);
                        // Reconstruct reg_to node:
                        for node_idx in interference_graph.node_indices() {
                            reg_to_node.insert(interference_graph[node_idx].clone(), node_idx);
                        }

                        // This needs to be cleaned up
                        old_to_new_reg.insert(r1.clone(), r2.clone());
                        inst_index.insert(old_index, new_index);
                        old_index += 1;
                        for reg in old_to_new_reg.keys() {
                            let mut temp = reg;
                            while let Some(t) = old_to_new_reg.get(temp) {
                                temp = t;
                            }
                            full_map.insert(reg.clone(), temp.clone());
                        }
                        for op in &mut ops.iter_mut() {
                            op.opcode = op.opcode.update_register(&full_map, &HashMap::new());
                        }

                        for op in &mut buf {
                            op.opcode = op.opcode.update_register(&full_map, &HashMap::new());
                        }
                    }
                } else {
                    inst_index.insert(old_index, new_index);
                    buf.push(ops[i].clone());
                    old_index += 1;
                    new_index += 1;
                }
            } else {
                inst_index.insert(old_index, new_index);
                buf.push(ops[i].clone());
                old_index += 1;
                new_index += 1;
            }
        } else if let VirtualOp::DataSectionOffsetPlaceholder = &ops[i].opcode {
            old_index += 2;
            new_index += 2;
            inst_index.insert(old_index - 2, new_index - 2);
            inst_index.insert(old_index - 1, new_index - 1);
            buf.push(ops[i].clone());
        } else if let VirtualOp::LWDataId(_, ref data_id) = &ops[i].opcode {
            inst_index.insert(old_index, new_index);
            buf.push(ops[i].clone());
            let type_of_data = data_section.type_of_data(data_id).expect(
            "Internal miscalculation in data section -- data id did not match up to any actual data",);
            if type_of_data.stack_size_of() > 1 {
                old_index += 2;
                new_index += 2;
            } else {
                old_index += 1;
                new_index += 1;
            }
        } else {
            inst_index.insert(old_index, new_index);
            buf.push(ops[i].clone());
            old_index += 1;
            new_index += 1;
        }
    }
    inst_index.insert(old_index, new_index);
    for op in &mut buf {
        op.opcode = op.opcode.update_register(&full_map, &inst_index);
    }

    buf
}

pub(crate) fn simplify(
    interference_graph: &mut Graph<VirtualRegister, (), petgraph::Undirected>,
    k: usize,
) -> Vec<(VirtualRegister, BTreeSet<VirtualRegister>)> {
    let mut stack: Vec<(VirtualRegister, BTreeSet<VirtualRegister>)> = vec![];

    while let Some(node) = pick_node(interference_graph, k) {
        let neighbors = interference_graph
            .neighbors(node)
            .map(|n| interference_graph[n].clone())
            .collect();
        stack.push((interference_graph.remove_node(node).unwrap(), neighbors));
    }

    // Gotta check for k colourability here as well

    stack
}

pub(crate) fn pick_node(
    interference_graph: &Graph<VirtualRegister, (), petgraph::Undirected>,
    k: usize,
) -> Option<NodeIndex> {
    for n in interference_graph.node_indices() {
        if let VirtualRegister::Virtual(_) = interference_graph[n] {
            if interference_graph.neighbors(n).count() < (k) {
                return Some(n);
            }
        }
    }
    None
}
