//! This module contains the non-user facing types for the string formatter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParamType {
    Int,
    Str,
}

#[derive(Debug, Clone, Copy)]
pub struct Flags(pub usize);
impl Flags {
    pub const SIGN: Self = Self(1);
    pub const SPACE: Self = Self(2);
    pub const PREFIX: Self = Self(4);
    pub const LEFT: Self = Self(8);
    pub const ZERO: Self = Self(16);
    pub const NONE: Self = Self(0);
    pub fn contains(&self, s: Self) -> bool {
        self.0 & s.0 != 0
    }
}
impl std::ops::Add for Flags {
    type Output = Self;
    fn add(mut self, b: Self) -> Self {
        self.0 += b.0;
        self
    }
}
impl std::iter::Sum for Flags {
    fn sum<I: Iterator<Item = Self>>(i: I) -> Self {
        i.fold(Flags::NONE, |s, n| s + n)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Var(pub usize);
static mut VARS: [i32; 52] = [0; 52];
impl Var {
    pub fn set(&self, v: i32) {
        unsafe { VARS[self.0] = v }
    }
    pub fn get(&self) -> i32 {
        unsafe { VARS[self.0] }
    }
}

#[derive(Clone, Copy)]
pub struct Maybe(Option<bool>);
impl Maybe {
    pub fn new() -> Self {
        Maybe(None)
    }
    pub fn yes(&mut self) -> Result<(), ()> {
        if self.0 == Some(false) {
            Err(())
        } else {
            self.0 = Some(true);
            Ok(())
        }
    }
    pub fn no(&mut self) -> Result<(), ()> {
        if self.0 == Some(true) {
            Err(())
        } else {
            self.0 = Some(false);
            Ok(())
        }
    }
}

#[derive(Debug, Clone)]
pub enum Cmd {
    Print(String),
    Int(Flags, usize, usize),
    Oct(Flags, usize, usize),
    LowerHex(Flags, usize, usize),
    UpperHex(Flags, usize, usize),
    Str(Flags, usize, Option<usize>),
    Char,
    Push(usize),
    Set(Var),
    Get(Var),
    Const(i32),
    StrLen,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Greater,
    Less,
    And,
    Or,
    Not,
    BitNot,
    ANSIFix,
    If,
    Then,
    Else,
    Fi,
}
