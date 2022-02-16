script;
use core::*;
use std::chain::assert;

fn sum_test(a:u64, b:u64, c:u64) -> u64 {
    let sum = a + b + c;
    sum
}

fn reassignment_test(cond: bool) -> u64 {
    let mut b = 2;
    if cond {
        b = 82;
    } else {
        b = 5;
    };
    b
}

fn loop_test() -> u64 {
    let mut b = 0;
    let trip_count = 10;
    while b < trip_count {
        b = b + 1;
    }
    b + 1
}

fn main() -> u64 {
    let one = 4;
    let two = 3;
    let sum = one + two;
    assert(sum == 7);

    assert(loop_test() == 11);
    assert(reassignment_test(false) == 5);
    assert(sum_test(1, 2, 3) == 6);
    assert(sum_test(30, 20, 10) == 60);
    assert(sum_test(3, 2, 1) == 6);

    let res = reassignment_test(true);
    assert(res == 82);
    res
}
