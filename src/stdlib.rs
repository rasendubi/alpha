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
    let s = std::str::from_utf8(bytes).unwrap();
    AlphaString::new(s) as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_type_of(args: *const SVec) -> AnyPtr {
    let args = (*args).elements();
    let x = args[1];
    trace!("alpha_type_of({:?})", x);
    type_of(x) as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_i64_mul(args: *const SVec) -> AnyPtr {
    let args = (*args).elements();
    let x: *const AlphaI64 = args[1].cast();
    let y: *const AlphaI64 = args[2].cast();
    trace!("alpha_i64_mul({:?}, {:?})", *x, *y);
    let result = (*x).value * (*y).value;
    AlphaI64::allocate(result).cast()
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_f64_mul(args: *const SVec) -> AnyPtr {
    let args = (*args).elements();
    let x: *const AlphaF64 = args[1].cast();
    let y: *const AlphaF64 = args[2].cast();
    trace!("alpha_f64_mul({:?}, {:?})", *x, *y);
    let result = (*x).value * (*y).value;
    AlphaF64::allocate(result).cast()
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_any(args: *const SVec) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let args = (*args).elements();
    let x = args[1];
    trace!("alpha_print_any({:?})", x);
    let type_ = type_of(x);
    write!(stdout, "<{}@{:p}>", (*type_).name, x).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_void(args: *const SVec) -> AnyPtr {
    trace!("alpha_print_void()");
    // print nothing
    VOID.load() as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_i64(args: *const SVec) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let args = (*args).elements();
    let x = *args[1].cast::<AlphaI64>();
    trace!("alpha_print_i64({:?})", x);
    write!(stdout, "{}", x).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_f64(args: *const SVec) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let args = (*args).elements();
    let x = *args[1].cast::<AlphaF64>();
    trace!("alpha_print_f64({:?})", x);
    write!(stdout, "{}", x.value).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_string(args: *const SVec) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let args = (*args).elements();
    let x = args[1] as *const AlphaString;
    trace!("alpha_print_string({:?})", x);
    trace!("x = {:?}", *x);
    write!(stdout, "{}", *x).unwrap();
    VOID.load() as AnyPtr
}

#[tracing::instrument]
pub unsafe extern "C" fn alpha_print_datatype(args: *const SVec) -> AnyPtr {
    let mut stdout = STDOUT.lock().unwrap();
    let args = (*args).elements();
    let x = &*args[1].cast::<DataType>();
    trace!("alpha_print_datatype({:?})", x);
    write!(stdout, "{}", x).unwrap();
    VOID.load() as AnyPtr
}
