mod ast;

#[cfg(test)]
mod test;

#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
}

#[derive(Debug)]
enum ErrorKind { }

pub fn compile(source: &str) -> Result<String, Error> {
    panic!();
}
