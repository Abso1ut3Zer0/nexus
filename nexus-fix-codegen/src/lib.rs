//! Dictionary-driven code generator for `nexus-fix-codec`.
//!
//! Reads a FIX XML dictionary and emits typed, zero-copy decode/encode Rust for
//! its messages, fields, and repeating groups — named message types, named field
//! accessors, and typed field enums — built on the hand-written codec primitives
//! (`FieldReader`, `FrameFormatter`, ...).
//!
//! Intended to run from a `build.rs`:
//!
//! ```no_run
//! nexus_fix_codegen::generate()
//!     .dictionary("dict/fix44.xml")
//!     .out_dir(std::env::var("OUT_DIR").unwrap())
//!     .run()
//!     .expect("FIX codegen failed");
//! ```
//!
//! Multiple dictionaries generate into per-dictionary subdirectories. Errors
//! surface as [`CodegenError`] (I/O, [`ParseError`], or [`EmitError`]).

mod dict;
mod emit;

#[cfg(test)]
mod tests;

pub use dict::ParseError;
pub use emit::EmitError;

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Debug)]
pub enum CodegenError {
    Io(io::Error),
    Parse(ParseError),
    Emit(EmitError),
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => write!(f, "{e}"),
            Self::Parse(e) => write!(f, "{e}"),
            Self::Emit(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for CodegenError {}

impl From<io::Error> for CodegenError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<ParseError> for CodegenError {
    fn from(e: ParseError) -> Self {
        Self::Parse(e)
    }
}

impl From<EmitError> for CodegenError {
    fn from(e: EmitError) -> Self {
        Self::Emit(e)
    }
}

pub struct Config {
    dictionaries: Vec<PathBuf>,
    out_dir: PathBuf,
    rustfmt: bool,
}

pub fn generate() -> Config {
    Config::new()
}

impl Config {
    pub fn new() -> Self {
        Self {
            dictionaries: Vec::new(),
            out_dir: PathBuf::from("."),
            rustfmt: true,
        }
    }

    pub fn dictionary<P: AsRef<Path>>(mut self, path: P) -> Self {
        self.dictionaries.push(path.as_ref().to_path_buf());
        self
    }

    pub fn dictionaries<I, P>(mut self, paths: I) -> Self
    where
        I: IntoIterator<Item = P>,
        P: AsRef<Path>,
    {
        for p in paths {
            self.dictionaries.push(p.as_ref().to_path_buf());
        }
        self
    }

    pub fn out_dir<P: AsRef<Path>>(mut self, dir: P) -> Self {
        self.out_dir = dir.as_ref().to_path_buf();
        self
    }

    pub fn rustfmt(mut self, enabled: bool) -> Self {
        self.rustfmt = enabled;
        self
    }

    pub fn run(self) -> Result<(), CodegenError> {
        let multi = self.dictionaries.len() > 1;
        for dict_path in &self.dictionaries {
            let xml = fs::read_to_string(dict_path)?;
            let parsed = dict::parse(&xml)?;
            let files = emit::generate(&parsed)?;

            let target = if multi {
                let stem = dict_path
                    .file_stem()
                    .map_or_else(|| "fix".to_string(), |s| s.to_string_lossy().into_owned());
                self.out_dir.join(stem)
            } else {
                self.out_dir.clone()
            };
            fs::create_dir_all(&target)?;

            for file in files {
                let path = target.join(&file.name);
                fs::write(&path, file.source)?;
                if self.rustfmt {
                    run_rustfmt(&path);
                }
            }
        }
        Ok(())
    }
}

impl Default for Config {
    fn default() -> Self {
        Self::new()
    }
}

fn run_rustfmt(path: &Path) {
    let _ = Command::new("rustfmt")
        .arg("--edition")
        .arg("2024")
        .arg(path)
        .status();
}
