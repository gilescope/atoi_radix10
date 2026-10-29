#![no_main]
use std::fmt::Debug;
use std::str::FromStr;

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    fuzz_parse::<u128>(data)
});


fn fuzz_parse<T>(data: &[u8])
    where T: atoi_radix10::FromStrRadixHelper + Debug + FromStr<Err = std::num::ParseIntError>
{
    if let Ok(s) = String::from_utf8(data.to_vec()){
        let spec: Result<T, _> = s.parse();
        assert_eq!(spec.map_err(|e| e.kind().clone()), atoi_radix10::parse::<T>(&data).map_err(|e| e.kind));
    } else {
        //just make sure doesn't panic:
        let _result = atoi_radix10::parse::<T>(&data);
    }
}
