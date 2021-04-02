#![feature(test)]
extern crate test;

use parseint::*;
use test::{black_box, Bencher};

const EXAMPLE_TIMESTAMP: &str = "1585201087123789";
const EXPECTED_TIMESTAMP: u64 = 1585201087123789;


#[bench]
fn bench_str_parse(b: &mut Bencher) {
    assert_eq!(str_parse(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| str_parse(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_naive_chars(b: &mut Bencher) {
    assert_eq!(naive_chars(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| naive_chars(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_naive_chars_iter(b: &mut Bencher) {
    assert_eq!(naive_chars_iter(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| naive_chars_iter(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_naive_chars_and(b: &mut Bencher) {
    assert_eq!(naive_chars_and(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| naive_chars_and(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_naive_bytes(b: &mut Bencher) {
    assert_eq!(naive_bytes(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| naive_bytes(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_naive_bytes_iter(b: &mut Bencher) {
    assert_eq!(naive_bytes_iter(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| naive_bytes_iter(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_naive_bytes_and(b: &mut Bencher) {
    assert_eq!(naive_bytes_and(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| naive_bytes_and(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_naive_bytes_and_c16(b: &mut Bencher) {
    assert_eq!(naive_bytes_and_c16(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| naive_bytes_and_c16(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_unrolled(b: &mut Bencher) {
    assert_eq!(unrolled(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| unrolled(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_unrolled_unsafe(b: &mut Bencher) {
    assert_eq!(unrolled_unsafe(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| unrolled_unsafe(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_unrolled_safe(b: &mut Bencher) {
    assert_eq!(unrolled_safe(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| unrolled_safe(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_trick(b: &mut Bencher) {
    assert_eq!(trick(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| trick(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_trick_with_checks(b: &mut Bencher) {
    assert_eq!(trick_with_checks(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| trick_with_checks(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_trick_with_checks_small_u64(b: &mut Bencher) {
    assert_eq!(parse_u64(":1234"), Err(()));
    assert_eq!(trick_with_checks("12345"), 12345u64);
    assert_eq!(parse_u64("1234/"), Err(()));
    assert_eq!(trick_with_checks("1234"), 1234u64);
    b.bytes = "1234".len() as u64;
    b.iter(|| trick_with_checks(black_box("1234")));
}

#[bench]
fn bench_trick_with_checks_i64(b: &mut Bencher) {
    assert_eq!(trick_with_checks_i64(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP as i64);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| trick_with_checks_i64(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_trick_128(b: &mut Bencher) {
    assert_eq!(trick_128(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| trick_128(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_trick_simd(b: &mut Bencher) {
    assert_eq!(trick_simd(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| trick_simd(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_trick_simd_8(b: &mut Bencher) {
    assert_eq!(trick_simd_8(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| trick_simd_8(black_box(EXAMPLE_TIMESTAMP)));
}

#[bench]
fn bench_trick_simd_c16(b: &mut Bencher) {
    assert_eq!(trick_simd_c16(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
    b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
    b.iter(|| trick_simd_c16(black_box(EXAMPLE_TIMESTAMP)));
}
