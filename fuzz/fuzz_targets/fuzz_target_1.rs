#![no_main]
#![feature(int_error_matching)]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = String::from_utf8(data.to_vec()){
        let spec: Result<u32, _> = s.parse();
        //assert_eq!(spec.map_err(|e| e.kind().clone()), atoi_radix10::parse_u32(&data).map_err(|e| e.kind));
        assert_eq!(spec.map_err(|_e| ()), atoi_radix10::parse_u32(&data).map_err(|_e| ()));
    } else {
        //just make sure doesn't panic:
        atoi_radix10::parse_u32(&data);
    }
});
