use libc::{c_int, strerror_r};
use std::ffi::CStr;

//-------------------------------

pub fn error_string(errno: i32) -> String {
    let mut buf = [0_i8; 512];

    let p = buf.as_mut_ptr();
    unsafe {
        if strerror_r(errno as c_int, p, buf.len()) < 0 {
            panic!("strerror_r failure");
        }

        let p = p as *const _;
        std::str::from_utf8(CStr::from_ptr(p).to_bytes())
            .unwrap()
            .to_owned()
    }
}

//-------------------------------
