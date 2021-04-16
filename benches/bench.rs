use criterion::BenchmarkId;
use criterion::Throughput;
use criterion::{criterion_group, criterion_main, Criterion};

use paste::paste;

use parseint::*;

macro_rules! ok_bench {
    ($target_type:ty, $meth:expr, $std_method:expr, $best_meth:expr, $values:expr) => {
        paste! {
            fn [<bench_parse_ $target_type>](c: &mut Criterion) {
                let mut group = c.benchmark_group(stringify!([<$meth>]));
                group //.sample_size(30)
                    .warm_up_time(std::time::Duration::from_millis(400))
                    .measurement_time(std::time::Duration::from_millis(2000));
                for num_str in $values.iter() {
                    let num : $target_type = num_str.parse().unwrap();
                    assert_eq!($meth(&num_str), Ok(num));
                    group.throughput(Throughput::Bytes(num_str.len() as u64));
                    group.bench_with_input(BenchmarkId::new("std", num), &num_str, |b, &val| {
                        b.iter(|| $std_method(&val));
                    });
                    group.bench_with_input(BenchmarkId::new("best", num), &num_str, |b, &val| {
                        b.iter(|| $best_meth(&val));
                    });
                    group.bench_with_input(BenchmarkId::new("new", num), &num_str, |b, &val| {
                        b.iter(|| $meth(&val));
                    });
                }
                group.finish();
            }
        }
    };
}

ok_bench!(
    u8,
    parse_u8,
    std_parse::<u8>,
    //cluatoi_parse_u8,
    parse_u8_best,
    ["1", "12", "123", "+200", &u8::MAX.to_string()]
);

ok_bench!(
    i8,
    parse_i8,
    std_parse::<i8>,
    //cluatoi_parse_u8,
    parse_i8_best,
    [&i8::MIN.to_string(), "-12", "-1", "1", "12", "123", "+100", &i8::MAX.to_string()]
);

ok_bench!(
    u16,
    parse_u16,
    std_parse::<u16>,
    parse_u16_best,
    //cluatoi_parse_u16,
    ["1", "12", "123", "1234", "12345",]
);

ok_bench!(
    u32,
    parse_u32,
    std_parse::<u32>,
    parse_u32_best,
    //cluatoi_parse_u32,
    [
        "1",
        "12",
        "123",
        "1234",
        "12345",
        "123456",
        "1234567",
        "12345678",
        "123456789",
        &u32::MAX.to_string()
    ]
);

ok_bench!(
    u64,
    parse_u64,
    std_parse::<u64>,
    parse_u64_best,
    [
        "1",
        "12",
        "123",
        "1234",
        "12345",
        "123456",
        "1234567",
        "12345678",
        "123456789",
        "1234567890",
        "12345678901",
        "123456789012",
        "1234567890123",
        "12345678901234",
        "123456789012345",
        "1234567890123456",
        "12345678901234567",
        "123456789012345678",
        "1234567890123456789",
        &u64::MAX.to_string()
    ]
);

ok_bench!(
    u128,
    parse_u128,
    std_parse::<u128>,
    parse_u128_best,
    [
        "1",
        "12",
        "123",
        "12345",
        "1234567",
        "123456789",
        "12345678901",
        "1234567890123",
        "123456789012345",
        "12345678901234567",
        "1234567890123456789",
        "123456789012345678901",
        "12345678901234567890123",
        "1234567890123456789012345",
        "123456789012345678901234567",
        "12345678901234567890123456789",
        "1234567890123456789012345678901",
        "123456789012345678901234567890123",
        "12345678901234567890123456789012345",
        "1234567890123456789012345678901234567",
        "123456789012345678901234567890123456789",
        &u128::MAX.to_string()
    ]
);

criterion_group!(
    benches,
    bench_parse_u8,
    bench_parse_u16,
    bench_parse_u32,
    bench_parse_u64,
    bench_parse_u128,
    bench_parse_i8,
);

criterion_main!(benches);

// #[bench]
// fn bench_trick_with_checks_i64(b: &mut Bencher) {
//     assert_eq!(
//         trick_with_checks_i64(EXAMPLE_TIMESTAMP),
//         EXPECTED_TIMESTAMP as i64
//     );
//     b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
//     b.iter(|| trick_with_checks_i64(black_box(EXAMPLE_TIMESTAMP)));
// }

// // #[bench]
// // fn bench_trick_128(b: &mut Bencher) {
// //     assert_eq!(trick_128(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
// //     b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
// //     b.iter(|| trick_128(black_box(EXAMPLE_TIMESTAMP)));
// // }

// // #[bench]
// // fn bench_trick_simd(b: &mut Bencher) {
// //     assert_eq!(trick_simd(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
// //     b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
// //     b.iter(|| trick_simd(black_box(EXAMPLE_TIMESTAMP)));
// // }

// // #[bench]
// // fn bench_trick_simd_8(b: &mut Bencher) {
// //     assert_eq!(trick_simd_8(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
// //     b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
// //     b.iter(|| trick_simd_8(black_box(EXAMPLE_TIMESTAMP)));
// // }

// // #[bench]
// // fn bench_trick_simd_c16(b: &mut Bencher) {
// //     assert_eq!(trick_simd_c16(EXAMPLE_TIMESTAMP), EXPECTED_TIMESTAMP);
// //     b.bytes = EXAMPLE_TIMESTAMP.len() as u64;
// //     b.iter(|| trick_simd_c16(black_box(EXAMPLE_TIMESTAMP)));
// // }
