use std::fmt;

#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub fn err(code_file: &str, code_line: u32, msg: &str) -> Error {
    Error(format!(
        "[ui_data:{}:{}] {}",
        code_file,
        code_line,
        msg,
    ))
}

impl std::error::Error for Error {}
