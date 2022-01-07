use std::fmt;

#[macro_export]
macro_rules! err {
    ( $x:expr ) => { err_inner(file!(), line!(), $x) };
}

#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub fn err_inner(file: &str, line: u32, msg: &str) -> Error {
    Error(format!("[{}:{}] {}", file, line, msg))
}


