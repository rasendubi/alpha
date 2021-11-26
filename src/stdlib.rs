use crate::gc;
use crate::types::*;

use std::io::Write;
use std::sync::Mutex;

use once_cell::sync::Lazy;
use tracing::trace;

pub static STDOUT: Lazy<Mutex<Box<dyn Write + Sync + Send>>> =
    Lazy::new(|| Mutex::new(Box::new(std::io::stdout())));

pub fn set_stdout(out: Box<dyn Write + Sync + Send>) {
    let mut stdout = STDOUT.lock().unwrap();
    *stdout = out;
}

extern "C" {
    // These seem to be provided by Rust runtime. Although I am not sure how much I should rely on
    // them.
    pub fn _Unwind_Resume();
    pub fn __gcc_personality_v0();
}

pub unsafe extern "C" fn gc_allocate(size: u64) -> *mut u8 {
    gc::allocate(size as usize)
}

pub unsafe extern "C" fn mk_str(p: *const u8, len: u64) -> AnyPtr {
    let bytes = std::slice::from_raw_parts(p, len as usize);
    let s = std::str::from_utf8(&bytes).unwrap();
    AlphaString::new(s) as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_f64_mul(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let x: *const AlphaF64 = *args.add(1).cast();
    let y: *const AlphaF64 = *args.add(2).cast();
    trace!("alpha_f64_mul({:?}, {:?})", *x, *y);
    let result = (*x).value * (*y).value;
    AlphaF64::allocate(result).cast()
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_i64_mul(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let x: *const AlphaI64 = *args.add(1).cast();
    let y: *const AlphaI64 = *args.add(2).cast();
    trace!("alpha_i64_mul({:?}, {:?})", *x, *y);
    let result = (*x).value * (*y).value;
    AlphaI64::allocate(result).cast()
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_type_of(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let x = *args.add(1);
    trace!("alpha_type_of({:?})", x);
    type_of(x) as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_any(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let x = *args.add(1) as AnyPtr;
    trace!("alpha_print_any({:?})", x);
    let type_ = type_of(x);
    write!(stdout, "<{}@{:p}>", (*type_).name, x).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_void(_n_args: i64, _args: *const AnyPtr) -> AnyPtr {
    trace!("alpha_print_void()");
    // print nothing
    VOID.load() as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_i64(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let x = *(*args.add(1) as *const i64);
    trace!("alpha_print_i64({:?})", x);
    write!(stdout, "{}", x).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_f64(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let x = *(*args.add(1) as *const AlphaF64);
    trace!("alpha_print_f64({:?})", x);
    write!(stdout, "{}", x.value).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_string(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let x = *args.add(1) as *const AlphaString;
    trace!("alpha_print_string({:?})", x);
    trace!("x = {:?}", *x);
    write!(stdout, "{}", *x).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_datatype(_n_args: i64, args: *const AnyPtr) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let x = &*(*args.add(1) as *const DataType);
    trace!("alpha_print_datatype({:?})", x);
    write!(stdout, "{}", x).unwrap();
    VOID.load() as AnyPtr
}
