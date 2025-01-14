script;

use std::b512::B512;

fn main() -> bool {
    let hi_bits: b256 = 0x7777777777777777777777777777777777777777777777777777777777777777;
    let lo_bits: b256 = 0x0000000000000000000000000000000000000000000000000000000000000000;


    let b = ~B512::from(hi_bits, lo_bits);
    let other_b = ~B512::new();
    (b.hi != other_b.hi) && (b.lo == other_b.lo)
}




