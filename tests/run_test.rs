use std::io;
use std::io::Write;
use std::sync::{Arc, Mutex, Once};

use alpha::{init, set_stdout, ExecutionSession};

#[allow(unused_macros)]
macro_rules! output_test {
    ( $name:ident, $in:expr, $out:expr ) => {
        #[test]
        #[::serial_test::serial]
        fn $name() {
            let out = $crate::run_test::run_output_test($in);
            assert_eq!(out, $out);
        }
    };
}

pub fn run_output_test(input: &str) -> String {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        pretty_env_logger::init();
        init();
    });

    let mut es = ExecutionSession::new();

    let buf = Buffer::new();
    set_stdout(Box::new(buf.clone()));

    es.eval(input).unwrap();

    let mut b = buf.0.lock().unwrap();
    let mut v = Vec::new();
    std::mem::swap(&mut *b, &mut v);
    String::from_utf8(v).unwrap()
}

#[derive(Debug, Clone)]
struct Buffer(Arc<Mutex<Vec<u8>>>);

impl Buffer {
    fn new() -> Self {
        Buffer(Arc::new(Mutex::new(Vec::new())))
    }
}

impl Write for Buffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.lock().unwrap().write(buf)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.0.lock().unwrap().flush()
    }
}
