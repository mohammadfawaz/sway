script;
use core::*;
use std::chain::assert;

/*fn sum_test(a:u64, b:u64, c:u64) -> u64 {
    let sum = a + b + c;
    sum
}

fn reassignment_test(cond: bool) -> u64 {
    let mut b = 2;
    if cond {
        b = 3;
    } else {
        b = 5;
    };
    b
}*/

fn loop_test(trip_count:u64) -> u64 {
    let mut b = 0;
    while b < trip_count {
        b = b + 1;
    }
    b
}

fn main() {
//    assert(sum_test(1, 2, 3) == 6);
//    assert(sum_test(3, 2, 1) == 6);
//    assert(sum_test(30, 20, 10) == 60);
//    assert(reassignment_test(true) == 3);
//    assert(reassignment_test(false) == 5);
    assert(loop_test(10) == 10);
}
