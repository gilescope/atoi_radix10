use criterion::black_box;
use criterion::BenchmarkId;
use criterion::Throughput;
use criterion::{criterion_group, criterion_main, Criterion};
//use criterion_cycles_per_byte::CyclesPerByte;
use paste::paste;

use atoi_radix10::*;

#[cfg(feature = "std")]
pub fn std_parse<T>(s: &str) -> Result<T, ()>
where
    T: core::str::FromStr,
{
    s.parse().map_err(|_| ())
}

macro_rules! ok_bench {
    ($target_type:ty, $prefix:literal,  $values:expr) => {
        paste! {
            fn [<bench_parse_ $prefix $target_type>](c: &mut Criterion//<CyclesPerByte>
                      ) {
                let mut group = c.benchmark_group(stringify!([<$prefix $target_type>]));

                group //.sample_size(30)
                    .warm_up_time(core::time::Duration::from_millis(500));
                //    .measurement_time(core::time::Duration::from_millis(2000));
                for num_str in $values.iter() {
                    let num : $target_type = num_str.parse().unwrap();
                    group.throughput(Throughput::Bytes(num_str.len() as u64));
                    #[cfg(feature="std")]
                    group.bench_with_input(BenchmarkId::new(format!("{}std",$prefix), num), &num_str, |b, &val| {
                        b.iter(|| std_parse::<$target_type>(&val).map_err(|_| ()));
                    });
                    // group.bench_with_input(BenchmarkId::new(format!("{}challenger",$prefix), num), &num_str, |b, &val| {
                    //     b.iter(|| $challenger_meth(val.as_bytes()));
                    // });
                    group.bench_with_input(BenchmarkId::new(format!("{}generic",$prefix), num), &num_str, |b, &val| {
                        b.iter(|| atoi_radix10::parse::<$target_type>(val.as_bytes()).map_err(|_| ()));
                    });
                    // group.bench_with_input(BenchmarkId::new(format!("{}challenger",$prefix), num), &num_str, |b, &val| {
                    //     b.iter(|| atoi_radix10::parse_challenger::<$target_type>(val.as_bytes()));
                    // });
                    //super::parse::<u16>(s).map_err(|_| PIE { kind: InvalidDigit })
                    // group.bench_with_input(BenchmarkId::new(format!("{}atoi_radix10",$prefix), num), &num_str, |b, &val| {
                    //     b.iter(|| $meth(val.as_bytes()));
                    // });
                    assert_eq!(atoi_radix10::parse::<$target_type>(num_str.as_bytes()), Ok(num), " when atoi_radix10 parsing {}", num_str);
                    assert_eq!(atoi_radix10::parse_challenger::<$target_type>(num_str.as_bytes()), Ok(num), " when challenger parsing {}", num_str);
                }
                group.finish();
            }
        }
    };
}

fn parse_chars_bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_16_chars_bench_group");
    //group //.sample_size(30)
    //    .warm_up_time(core::time::Duration::from_millis(1000))
    //    .measurement_time(core::time::Duration::from_millis(2000));
    let num_str = "12345678123456781234567812345678";
    group.throughput(Throughput::Bytes(num_str.len() as u64));
    group.bench_with_input(BenchmarkId::new("32", num_str), &num_str, |b, &_val| {
        b.iter(|| parse_32_chars(black_box(num_str.as_bytes())));
    });
    let num_str = "1234567812345678";
    group.throughput(Throughput::Bytes(num_str.len() as u64));
    group.bench_with_input(BenchmarkId::new("16", num_str), &num_str, |b, &_val| {
        b.iter(|| parse_16_chars(black_box(num_str.as_bytes())));
    });
    let num_str = "12345678";
    assert_eq!(parse_8_chars(num_str.as_bytes()), Ok(12345678));
    group.throughput(Throughput::Bytes(num_str.len() as u64));
    group.bench_with_input(BenchmarkId::new("8", num_str), &num_str, |b, &_val| {
        b.iter(|| parse_8_chars(black_box(num_str.as_bytes())));
    });
    // let num_str = "123456";
    // assert_eq!(parse_6_chars(num_str.as_bytes()), Ok(123456));
    // group.throughput(Throughput::Bytes(num_str.len() as u64));
    // group.bench_with_input(BenchmarkId::new("6", num_str), &num_str, |b, &_val| {
    //     b.iter(|| parse_6_chars(black_box(num_str.as_bytes())));
    // });
    let num_str = "1234";
    group.throughput(Throughput::Bytes(num_str.len() as u64));
    group.bench_with_input(BenchmarkId::new("4", num_str), &num_str, |b, &_val| {
        b.iter(|| parse_4_chars(black_box(num_str.as_bytes())));
    });
    let num_str = "12";
    group.throughput(Throughput::Bytes(num_str.len() as u64));
    group.bench_with_input(BenchmarkId::new("2", num_str), &num_str, |b, &_val| {
        b.iter(|| parse_2_chars(black_box(num_str.as_bytes())));
    });

    group.finish();
}

ok_bench!(u8, "", ["1", "12", "123", "+200", &u8::MAX.to_string()]);

ok_bench!(i8, "pos_", ["1", "12", "123", "+100", &i8::MAX.to_string()]);

ok_bench!(i8, "neg_", [&i8::MIN.to_string(), "-12", "-1"]);

ok_bench!(u16, "", ["1", "12", "123", "1234", "12345",]);

ok_bench!(
    i16,
    "pos_",
    //[&i16::MIN.to_string(), "-1234", "-123", "-12","-1", "1", "12", "123", "1234", &i16::MAX.to_string(),"+12345"]
    //[&i16::MIN.to_string(), "-1234", "-123", "-12","-1"]
    ["1", "12", "123", "1234", "12345", "+12345"]
);

ok_bench!(
    i16,
    "neg_",
    //[&i16::MIN.to_string(), "-1234", "-123", "-12","-1", "1", "12", "123", "1234", &i16::MAX.to_string(),"+12345"]
    [&i16::MIN.to_string(), "-1234", "-123", "-12", "-1"] //["1", "12", "123", "1234", &i16::MAX.to_string(),"+12345"]
);

ok_bench!(
    u32,
    "",
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
    i32,
    "pos_",
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
        &i32::MAX.to_string()
    ]
);

ok_bench!(
    i32,
    "neg_",
    [
        "-1",
        "-12",
        "-123",
        "-1234",
        "-12345",
        "-123456",
        "-1234567",
        "-12345678",
        "-123456789",
        &i32::MIN.to_string()
    ]
);

ok_bench!(
    u64,
    "",
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
    i64,
    "pos_",
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
        &i64::MAX.to_string()
    ]
);

ok_bench!(
    i64,
    "neg_",
    [
        "-1",
        "-12",
        "-123",
        "-1234",
        "-12345",
        "-123456",
        "-1234567",
        "-12345678",
        "-123456789",
        "-1234567890",
        "-12345678901",
        "-123456789012",
        "-1234567890123",
        "-12345678901234",
        "-123456789012345",
        "-1234567890123456",
        "-12345678901234567",
        "-123456789012345678",
        "-1234567890123456789",
        &i64::MIN.to_string()
    ]
);

ok_bench!(
    u128,
    "",
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

ok_bench!(
    i128,
    "pos_",
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
        &i128::MAX.to_string()
    ]
);

ok_bench!(
    i128,
    "neg_",
    [
        "-1",
        "-12",
        "-123",
        "-12345",
        "-1234567",
        "-123456789",
        "-12345678901",
        "-1234567890123",
        "-123456789012345",
        "-12345678901234567",
        "-1234567890123456789",
        "-123456789012345678901",
        "-12345678901234567890123",
        "-1234567890123456789012345",
        "-123456789012345678901234567",
        "-12345678901234567890123456789",
        "-1234567890123456789012345678901",
        "-123456789012345678901234567890123",
        "-12345678901234567890123456789012345",
        "-1234567890123456789012345678901234567",
        "-123456789012345678901234567890123456789",
        &i128::MIN.to_string()
    ]
);

criterion_group!(
    name = benches;
    config = Criterion::default();//.with_measurement(CyclesPerByte);
    targets =
    bench_parse_u8,
    bench_parse_u16,
    bench_parse_u32,
    bench_parse_u64,
    bench_parse_u128,
    bench_parse_pos_i8,
    bench_parse_neg_i8,
    bench_parse_pos_i16,
    bench_parse_neg_i16,
    bench_parse_pos_i32,
    bench_parse_neg_i32,
    bench_parse_pos_i64,
    bench_parse_neg_i64,
    bench_parse_pos_i128,
    bench_parse_neg_i128,
    parse_chars_bench,
);

criterion_main!(benches);
