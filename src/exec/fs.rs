//! Tools for giving the emulator access to files.

use std::io::{Error, ErrorKind, Cursor, SeekFrom, Read, Write, Seek};
use std::sync::{Arc, Mutex};

/// The types of errors for client-level file operations.
#[derive(Debug)]
pub enum FileError {
    /// A client-level permision violation.
    /// Returning this error constitutes a hard client error, halting the emulator.
    Permissions,
    /// A real IO error.
    /// Returning this error constitutes a soft failure,
    /// which for standard IO system calls means they just return `-1` and emulator execution continues.
    IOError(Error),
}
impl From<Error> for FileError {
    fn from(err: Error) -> FileError {
        FileError::IOError(err)
    }
}

/// All features of files that are exposed to client programs.
/// 
/// `is_readable` and `is_writable` inform the emulator what file permissions should be 
pub trait FileHandle {
    /// A special flag used in the event that `read` returns zero (see `read`).
    fn is_interactive(&self) -> bool;

    /// Reads at most enough data to fill `buf` and returns the number of bytes read.
    /// Returning zero implies EOF unless `is_interactive` is true,
    /// in which case the emulator would enter the suspended read state awaiting more data.
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, FileError>;
    /// Writes all the content of `buf` to the file.
    fn write_all(&mut self, buf: &[u8]) -> Result<(), FileError>;
    /// Sets the internal read/write cursor to `pos` and returns the new absolute position.
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, FileError>;
}

/// Represents a file that is stored entirely in memory.
/// 
/// The data is backed by a `Cursor<Vec<u8>>`, which is stored via `Arc<Mutex<T>>` so that it can be accessed externally, even across threads.
/// The `readable`, `writable`, and `seekable` fields control client-level file permissions.
/// If `appendonly` is set to `true`, then the file will seek to the end before each write operation.
/// 
/// The `interactive` field should be set to `true` if additional data may be added to `content`, and otherwise should be `false`.
/// `interactive` should never transition from `false` to `true`.
/// If an interactive file later becomes non-interactive (e.g. forced EOF), then `interactive` should transition from `true` to `false`.
pub struct MemoryFile {
    pub content: Arc<Mutex<Cursor<Vec<u8>>>>,
    pub readable: bool,
    pub writable: bool,
    pub seekable: bool,
    pub appendonly: bool,
    pub interactive: bool,
}
impl FileHandle for MemoryFile {
    fn is_interactive(&self) -> bool { self.interactive }

    fn read(&mut self, buf: &mut [u8]) -> Result<usize, FileError> {
        if !self.readable { return Err(FileError::Permissions); }
        let mut h = self.content.lock().unwrap();
        let mut written = 0;
        loop {
            match h.read(&mut buf[written..]) {
                Ok(count) => {
                    written += count;
                    if written >= buf.len() || count == 0 { return Ok(written); } // stop when we fill buf or if we got nothing
                }
                Err(e) => match e.kind() {
                    ErrorKind::Interrupted => (), // just retry if interrupted
                    _ => return Err(e.into()),
                }
            }
        }
    }
    fn write_all(&mut self, buf: &[u8]) -> Result<(), FileError> {
        if !self.writable { return Err(FileError::Permissions); }
        let mut f = self.content.lock().unwrap();
        if self.appendonly { f.seek(SeekFrom::End(0))?; }
        f.write_all(buf)?;
        Ok(())
    }
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, FileError> {
        if !self.seekable { return Err(FileError::Permissions); }
        Ok(self.content.lock().unwrap().seek(pos)?)
    }
}