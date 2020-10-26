//! `format` provides the formatting macro `tparm!(...)` and related types.

mod types;
use types::*;

#[macro_use]
mod macros;

/// The [`TerminfoString`](struct.TerminfoString.html) struct represents a terminfo string
/// capability which has been parsed as a format string.
///
/// The primary use of TerminfoString is to prepare a format string so that it can be reused
/// several times.
///
/// Example
/// -------
/// ```rust, no_run
/// use binary_terminfo::*;
/// fn main() -> Result<(), std::io::Error> {
///     let terminfo = Terminfo::default()?;
///
///     let sgr = TerminfoString::from_string(terminfo.get_str(StringCap::SetAttributes).unwrap().into())?;
///     let sgr0 = terminfo.get_str(StringCap::ExitAttributeMode).unwrap();
///     println!("{}bold{}", tparm!(sgr, 0,0,0,0,0,1,0,0,0)?, sgr0);
///     println!("{}underline{}", tparm!(sgr, 0,1,0,0,0,0,0,0,0)?, sgr0);
///
///     Ok(())
/// }
/// ```
#[derive(Debug, Clone)]
pub struct TerminfoString {
    cmds: Vec<Cmd>,
    sig: Vec<Option<ParamType>>,
    orig: String,
}
impl TerminfoString {
    /// Parses a `String` as a format string to make a [`TerminfoString`](struct.TerminfoString.html)
    ///
    /// See struct-level documentation for an example.
    pub fn from_string(s: String) -> Result<Self, Error> {
        let mut state = ParseState::new();
        let parsed = parse!(
            parse (s) or Error {
                rule __top__ -> Cmd {
                    ['%'] {
                        ['%'] => { Cmd::Print("%".into()) }
                        ?=[':'|'#'|' '|'0'..='9'|'.'|'s'|'d'|'o'|'x'|'X'] {
                            [':']? {
                                <flags>? as f {
                                    <nat>? as w {
                                        ['.']? {
                                            <nat>? as p {
                                                ['d'] => { Cmd::Int(f.unwrap_or(Flags::NONE),w.unwrap_or(0),p.unwrap_or(0)) }
                                                ['o'] => { Cmd::Oct(f.unwrap_or(Flags::NONE),w.unwrap_or(0),p.unwrap_or(0)) }
                                                ['x'] => { Cmd::LowerHex(f.unwrap_or(Flags::NONE),w.unwrap_or(0),p.unwrap_or(0)) }
                                                ['X'] => { Cmd::UpperHex(f.unwrap_or(Flags::NONE),w.unwrap_or(0),p.unwrap_or(0)) }
                                                ['s'] => { Cmd::Str(f.unwrap_or(Flags::NONE),w.unwrap_or(0),p) }
                                                _ =>(s) {Err(Error::UnknownFormat(s.into()))?}
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        ['c'] => { Cmd::Char }
                        ['p'] {
                            [p @ '1'..='9'] => { Cmd::Push(p as usize - '1' as usize) }
                            _ =>(s) {Err(Error::UnknownFormat(s.into()))?}
                        }
                        ['P'] {
                            <var> as var => { Cmd::Set(var) }
                            _ =>(s) {Err(Error::UnknownFormat(s.into()))?}
                        }
                        ['g'] {
                            <var> as var => { Cmd::Get(var) }
                            _ =>(s) {Err(Error::UnknownFormat(s.into()))?}
                        }
                        ['\''] {
                            [c] {
                                ['\''] => { Cmd::Const(c as i32) }
                                _ =>(s) {Err(Error::UnknownFormat(s.into()))?}
                            }
                        }
                        ['{'] {
                            <int> as n {
                                ['}'] => { Cmd::Const(n) }
                                _ =>(s) {Err(Error::UnknownFormat(s.into()))?}
                            }
                            _ =>(s) {Err(Error::UnknownFormat(s.into()))?}
                        }
                        ['l'] => { Cmd::StrLen }
                        ['+'] => { Cmd::Add }
                        ['-'] => { Cmd::Sub }
                        ['*'] => { Cmd::Mul }
                        ['/'] => { Cmd::Div }
                        ['m'] => { Cmd::Rem }
                        ['&'] => { Cmd::BitAnd }
                        ['|'] => { Cmd::BitOr }
                        ['^'] => { Cmd::BitXor }
                        ['='] => { Cmd::Eq }
                        ['>'] => { Cmd::Greater }
                        ['<'] => { Cmd::Less }
                        ['A'] => { Cmd::And }
                        ['O'] => { Cmd::Or }
                        ['!'] => { Cmd::Not }
                        ['~'] => { Cmd::BitNot }
                        ['i'] => { Cmd::ANSIFix }
                        ['?'] => { Cmd::If }
                        ['t'] => { Cmd::Then }
                        ['e'] => { Cmd::Else }
                        [';'] => { Cmd::Fi }
                        _ =>(s) {Err(Error::UnknownFormat(s.into()))?}
                    }
                    .. =>(s) {Cmd::Print(s.into())}
                }
                rule int -> i32 {
                    ['-']? {
                        ['0'..='9']+ =>(n) { n.parse().unwrap() }
                    }
                }
                rule nat -> usize {
                    ['0'..='9']+ =>(n) { n.parse().unwrap() }
                }
                rule flags -> Flags {
                    <flag>+ as f {
                        ['0'] => {Flags::ZERO + f.drain(..).sum()}
                        ?=_ => {f.drain(..).sum()}
                    }
                    ['0'] => {Flags::ZERO}
                }
                rule flag -> Flags {
                    ['+'] => {Flags::SIGN}
                    [' '] => {Flags::SPACE}
                    ['#'] => {Flags::PREFIX}
                    ['-'] => {Flags::LEFT}
                }
                rule var -> Var {
                    [v @ 'a'..='z'] => { Var(v as usize - 'a' as usize) }
                    [v @ 'A'..='Z'] => { Var(v as usize - 'A' as usize + 26) }
                }
            }
        );
        for cmd in parsed.into_iter() {
            state.push_cmd(cmd)?;
        }
        Ok(TerminfoString {
            cmds: state.cmds,
            sig: state.sig,
            orig: s,
        })
    }
    /// Applies the format to a set of parameters.
    ///
    /// It is cleaner to use [`tparm`](../macros.tparm.html) for this.
    ///
    /// Example
    /// -------
    /// ```rust
    /// use binary_terminfo::*;
    /// fn main() -> Result<(), binary_terminfo::format::Error> {
    ///     let s = TerminfoString::from_string("Hello, %s".into())?;
    ///
    ///     assert_eq!(s.fmt(vec![&"Barry"])?, "Hello, Barry");
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn fmt(&self, v: Vec<&dyn Param>) -> Result<String, Error> {
        if self.sig.len() > v.len() {
            return Err(Error::NotEnoughParams);
        }
        for (n, (ty, param)) in self.sig.iter().zip(&v).enumerate() {
            if let Some(ty) = ty {
                if param.ty() != *ty {
                    return Err(Error::IncorrectType {
                        param: n,
                        expected: *ty,
                    });
                }
            }
        }

        use std::fmt::Write;
        let mut r = String::new();
        let mut stack: Vec<Box<dyn Param>> = vec![];
        let mut ansifix = 0;
        let mut cond: Vec<Option<bool>> = vec![];
        for cmd in &self.cmds {
            if cond.last().copied().unwrap_or(Some(true)).unwrap_or(false) {
                match cmd {
                    Cmd::Print(s) => r.push_str(&s),
                    Cmd::Push(n) => match v[*n].ty() {
                        ParamType::Int => {
                            stack.push(Box::new(v[*n].int() + ansifix * (*n < 2) as i32))
                        }
                        ParamType::Str => stack.push(Box::new(v[*n].str())),
                    },
                    Cmd::Int(f, w, p) => {
                        let n = stack.pop().unwrap().int();
                        let sign = if n >= 0 {
                            if f.contains(Flags::SIGN) {
                                "+"
                            } else if f.contains(Flags::SPACE) {
                                " "
                            } else {
                                ""
                            }
                        } else {
                            "-"
                        };
                        let value = format!("{:0>p$}", n.abs(), p = p);
                        let w = w.saturating_sub(sign.len());
                        if f.contains(Flags::LEFT) {
                            write!(r, "{}{:<w$}", sign, value, w = w).unwrap();
                        } else if f.contains(Flags::ZERO) {
                            write!(r, "{}{:0>w$}", sign, value, w = w).unwrap();
                        } else {
                            write!(
                                r,
                                "{:>w$}{}{}",
                                "",
                                sign,
                                value,
                                w = w.saturating_sub(value.len())
                            )
                            .unwrap();
                        }
                    }
                    Cmd::Oct(f, w, p) | Cmd::LowerHex(f, w, p) | Cmd::UpperHex(f, w, p) => {
                        let n = stack.pop().unwrap().int();
                        let prefix = if f.contains(Flags::PREFIX) {
                            match cmd {
                                Cmd::Oct(_, _, _) => "0",
                                Cmd::LowerHex(_, _, _) => "0x",
                                Cmd::UpperHex(_, _, _) => "OX",
                                _ => panic!(),
                            }
                        } else {
                            ""
                        };
                        let value = match cmd {
                            Cmd::Oct(_, _, _) => format!("{:0>p$o}", n, p = p),
                            Cmd::LowerHex(_, _, _) => format!("{:0>p$x}", n, p = p),
                            Cmd::UpperHex(_, _, _) => format!("{:0>p$X}", n, p = p),
                            _ => panic!(),
                        };
                        let w = w.saturating_sub(prefix.len());
                        if f.contains(Flags::LEFT) {
                            write!(r, "{}{:<w$}", prefix, value, w = w).unwrap();
                        } else if f.contains(Flags::ZERO) {
                            write!(r, "{}{:0>w$}", prefix, value, w = w).unwrap();
                        } else {
                            write!(
                                r,
                                "{:>w$}{}{}",
                                "",
                                prefix,
                                value,
                                w = w.saturating_sub(value.len())
                            )
                            .unwrap();
                        }
                    }
                    Cmd::Str(f, w, p) => {
                        let s = stack.pop().unwrap();
                        let s: String = if let Some(p) = p {
                            s.str().chars().take(*p).collect()
                        } else {
                            s.str().into()
                        };
                        if f.contains(Flags::LEFT) {
                            write!(r, "{:<w$}", s, w = w).unwrap();
                        } else {
                            write!(r, "{:>w$}", s, w = w).unwrap();
                        }
                    }
                    Cmd::Char => {
                        let c = stack.pop().unwrap().int() as u32;
                        r.push(std::char::from_u32(c).ok_or(Error::InvalidCharacter)?);
                    }
                    Cmd::Set(v) => v.set(stack.pop().unwrap().int()),
                    Cmd::Get(v) => stack.push(Box::new(v.get())),
                    Cmd::Const(c) => stack.push(Box::new(c)),
                    Cmd::StrLen => {
                        let l = stack.pop().unwrap().str().len() as i32;
                        stack.push(Box::new(l));
                    }
                    Cmd::Add => {
                        let r = stack.pop().unwrap().int();
                        let l = stack.pop().unwrap().int();
                        stack.push(Box::new(l.wrapping_add(r)));
                    }
                    Cmd::Sub => {
                        let r = stack.pop().unwrap().int();
                        let l = stack.pop().unwrap().int();
                        stack.push(Box::new(l.wrapping_sub(r)));
                    }
                    Cmd::Mul => {
                        let r = stack.pop().unwrap().int();
                        let l = stack.pop().unwrap().int();
                        stack.push(Box::new(l.wrapping_mul(r)));
                    }
                    Cmd::Div => {
                        let r = stack.pop().unwrap().int();
                        if r == 0 {
                            return Err(Error::DivByZero);
                        }
                        let l = stack.pop().unwrap().int();
                        stack.push(Box::new(l.wrapping_div(r)));
                    }
                    Cmd::Rem => {
                        let r = stack.pop().unwrap().int();
                        if r == 0 {
                            return Err(Error::DivByZero);
                        }
                        let l = stack.pop().unwrap().int();
                        stack.push(Box::new(l % r));
                    }
                    Cmd::BitAnd => {
                        let r = stack.pop().unwrap().int();
                        let l = stack.pop().unwrap().int();
                        stack.push(Box::new(l & r));
                    }
                    Cmd::BitOr => {
                        let r = stack.pop().unwrap().int();
                        let l = stack.pop().unwrap().int();
                        stack.push(Box::new(l | r));
                    }
                    Cmd::BitXor => {
                        let r = stack.pop().unwrap().int();
                        let l = stack.pop().unwrap().int();
                        stack.push(Box::new(l ^ r));
                    }
                    Cmd::Eq => {
                        let r = stack.pop().unwrap();
                        let l = stack.pop().unwrap();
                        stack.push(Box::new(l.is_equal(r.as_ref()) as i32));
                    }
                    Cmd::Greater => {
                        let r = stack.pop().unwrap().int();
                        let l = stack.pop().unwrap().int();
                        stack.push(Box::new((l > r) as i32));
                    }
                    Cmd::Less => {
                        let r = stack.pop().unwrap().int();
                        let l = stack.pop().unwrap().int();
                        stack.push(Box::new((l < r) as i32));
                    }
                    Cmd::And => {
                        let r = stack.pop().unwrap().so();
                        let l = stack.pop().unwrap().so();
                        stack.push(Box::new((l && r) as i32));
                    }
                    Cmd::Or => {
                        let r = stack.pop().unwrap().so();
                        let l = stack.pop().unwrap().so();
                        stack.push(Box::new((l || r) as i32));
                    }
                    Cmd::Not => {
                        let n = !stack.pop().unwrap().so();
                        stack.push(Box::new(n as i32));
                    }
                    Cmd::BitNot => {
                        let n = stack.pop().unwrap().int();
                        stack.push(Box::new(n ^ -1));
                    }
                    Cmd::ANSIFix => {
                        ansifix += 1;
                    }
                    Cmd::If => cond.push(Some(true)),
                    Cmd::Then => {
                        cond.last_mut().unwrap().replace(stack.pop().unwrap().so());
                    }
                    Cmd::Else => {
                        *cond.last_mut().unwrap() = None;
                    }
                    Cmd::Fi => {
                        cond.pop();
                    }
                }
            } else {
                match cmd {
                    Cmd::If => cond.push(None),
                    Cmd::Else => {
                        if let Some(Some(cond)) = cond.last_mut() {
                            *cond = true
                        }
                    }
                    Cmd::Fi => {
                        cond.pop();
                    }
                    _ => {}
                }
            }
        }
        Ok(r)
    }
}

/// A trait for types which can be used as a format string by `tparm!(...)`.
pub trait AsTerminfoString {
    fn as_terminfo_string(&self) -> Result<std::borrow::Cow<TerminfoString>, Error>;
}
impl AsTerminfoString for TerminfoString {
    fn as_terminfo_string(&self) -> Result<std::borrow::Cow<TerminfoString>, Error> {
        Ok(std::borrow::Cow::Borrowed(self))
    }
}
impl AsTerminfoString for &str {
    fn as_terminfo_string(&self) -> Result<std::borrow::Cow<TerminfoString>, Error> {
        TerminfoString::from_string(self.to_string()).map(|s| std::borrow::Cow::Owned(s))
    }
}
impl AsTerminfoString for String {
    fn as_terminfo_string(&self) -> Result<std::borrow::Cow<TerminfoString>, Error> {
        TerminfoString::from_string(self.clone()).map(|s| std::borrow::Cow::Owned(s))
    }
}

/// A trait unifying the parameter types for format strings.
pub trait Param {
    fn int(&self) -> i32;
    fn str(&self) -> &str;
    fn ty(&self) -> ParamType;
    fn is_equal(&self, o: &dyn Param) -> bool {
        match (self.ty(), o.ty()) {
            (ParamType::Int, ParamType::Int) => self.int() == o.int(),
            (ParamType::Str, ParamType::Str) => self.str() == o.str(),
            _ => false,
        }
    }
    fn so(&self) -> bool {
        !self.is_equal(&0)
    }
}
impl Param for i32 {
    fn int(&self) -> i32 {
        *self
    }
    fn str(&self) -> &str {
        panic!()
    }
    fn ty(&self) -> ParamType {
        ParamType::Int
    }
}
impl Param for &str {
    fn int(&self) -> i32 {
        panic!()
    }
    fn str(&self) -> &str {
        *self
    }
    fn ty(&self) -> ParamType {
        ParamType::Str
    }
}
impl Param for String {
    fn int(&self) -> i32 {
        panic!()
    }
    fn str(&self) -> &str {
        self
    }
    fn ty(&self) -> ParamType {
        ParamType::Str
    }
}
impl<T: Param> Param for &T {
    fn int(&self) -> i32 {
        (**self).int()
    }
    fn str(&self) -> &str {
        (**self).str()
    }
    fn ty(&self) -> ParamType {
        (**self).ty()
    }
}

/// The type of a formatting error.
#[derive(Clone)]
pub enum Error {
    /// The format string does not push enough values onto the stack.
    ///
    /// This error is not generated if the string never pushes any values onto the stack, since in
    /// this case the string is assumed to be a legacy termcap string.
    MissingPush,
    /// A `"%t"`, `"%e"` or `"%;"` appears outside the scope of a conditional.
    Unexpected(String),
    /// The format string uses a parameter as both an integer and a string.
    ParamBothTypes(usize),
    /// An unknown formatter is encountered.
    UnknownFormat(String),
    /// The format string uses more parameters than were provided to the formatter.
    NotEnoughParams,
    /// The type of a parameter did not match its usage in the format string.
    IncorrectType {
        param: usize,
        expected: ParamType,
    },
    /// An invalid integer value was provided to a '%c' formatter.
    InvalidCharacter,
    DivByZero,
}
impl From<Error> for std::io::Error {
    fn from(e: Error) -> std::io::Error {
        match e {
            Error::MissingPush
            | Error::Unexpected(_)
            | Error::ParamBothTypes(_)
            | Error::UnknownFormat(_) => std::io::ErrorKind::InvalidData.into(),
            _ => std::io::ErrorKind::InvalidInput.into(),
        }
    }
}
impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::MissingPush => write!(
                f,
                "Format string does not push enough values onto the stack."
            ),
            Error::Unexpected(s) => write!(f, "Unexpected '{}' in format string.", s),
            Error::ParamBothTypes(n) => write!(
                f,
                "Format string uses parameter {} as both a string and an integer.",
                n
            ),
            Error::UnknownFormat(s) => write!(f, "Unknown format {} in format string.", s),
            Error::NotEnoughParams => write!(f, "Not enough parameters for format string."),
            Error::IncorrectType { param, expected } => write!(
                f,
                "Parameter {} has the wrong type. Format expected {}.",
                param,
                match expected {
                    ParamType::Str => "a string",
                    ParamType::Int => "an integer",
                }
            ),
            Error::InvalidCharacter => write!(f, "Cannot format value as a character."),
            Error::DivByZero => write!(f, "Division by zero."),
        }
    }
}

/// The ParseState keeps track of the possible list of types on the stack, as well as the
/// parsed commands. There may be more than one possibility, for what's on the stack since
/// there are conditionals in format strings, but since there are unlikely to be many,
/// keeping track of all the possibilities shouldn't be particularly slow.
/// Doing it this way means that we accept format string/argument combinations that ncurses
/// wouldn't, but should treat accepted strings the same way as ncurses does.
#[derive(Clone)]
struct ParseState {
    stack: Vec<Vec<Option<usize>>>, // Current stack
    sig: Vec<Option<ParamType>>,    // Parameter Type list
    cmds: Vec<Cmd>,                 // Command List
    branches: Vec<Option<(Vec<Vec<Option<usize>>>, Vec<Vec<Option<usize>>>)>>, // (Stack when entering branch, stacks from previous branches)
    pushes: Maybe, // Does "Push" show up explicitly or is this termcap-style?
}
impl ParseState {
    fn new() -> Self {
        ParseState {
            stack: vec![vec![]],
            sig: vec![],
            cmds: vec![],
            branches: vec![],
            pushes: Maybe::new(),
        }
    }
    fn push(&mut self, p: Option<usize>) -> Result<(), ()> {
        self.pushes.yes()?;
        for s in &mut self.stack {
            s.push(p);
            if let Some(i) = p {
                while i >= self.sig.len() {
                    self.sig.push(None);
                }
            }
        }
        Ok(())
    }
    fn pop(&mut self, t: Option<ParamType>) -> Result<(), Error> {
        if self.pushes.no().is_ok() {
            self.cmds.push(Cmd::Push(self.sig.len()));
            self.sig.push(t);
            Ok(())
        } else {
            for i in self.stack.iter_mut().map(|s| s.pop()) {
                let i = i.ok_or(Error::MissingPush)?;
                if let Some(t) = t {
                    if let Some(i) = i {
                        if let Some(d) = self.sig[i].replace(t) {
                            if d != t {
                                return Err(Error::ParamBothTypes(i));
                            }
                        }
                    }
                }
            }
            Ok(())
        }
    }
    fn start_if(&mut self) {
        self.branches.push(None)
    }
    fn then(&mut self) -> Result<(), Error> {
        let c = self
            .branches
            .last_mut()
            .ok_or(Error::Unexpected(format!("%t")))?;
        c.replace((self.stack.clone(), vec![]));
        Ok(())
    }
    fn els(&mut self) -> Result<(), Error> {
        let c = self
            .branches
            .last_mut()
            .ok_or(Error::Unexpected(format!("%e")))?
            .as_mut()
            .ok_or(Error::Unexpected(format!("%e")))?;
        'o: for s in &self.stack {
            for t in &c.1 {
                if s == t {
                    continue 'o;
                }
            }
            c.1.push(s.clone());
        }
        self.stack = c.0.clone();
        Ok(())
    }
    fn end_if(&mut self) -> Result<(), Error> {
        let mut c = self
            .branches
            .pop()
            .ok_or(Error::Unexpected(format!("%;")))?
            .ok_or(Error::Unexpected(format!("%;")))?;
        'o: for s in &self.stack {
            for t in &c.1 {
                if s == t {
                    continue 'o;
                }
            }
            c.1.push(s.clone());
        }
        self.stack = c.1;
        Ok(())
    }
    fn push_cmd(&mut self, c: Cmd) -> Result<(), Error> {
        match &c {
            Cmd::Print(s) => {
                if let Some(Cmd::Print(p)) = self.cmds.last_mut() {
                    p.push_str(&s)
                } else {
                    self.cmds.push(c);
                }
            }
            Cmd::Int(_, _, _)
            | Cmd::Oct(_, _, _)
            | Cmd::LowerHex(_, _, _)
            | Cmd::UpperHex(_, _, _)
            | Cmd::Char
            | Cmd::Set(_) => {
                self.pop(Some(ParamType::Int))?;
                self.cmds.push(c);
            }
            Cmd::Str(_, _, __) => {
                self.pop(Some(ParamType::Str))?;
                self.cmds.push(c);
            }
            Cmd::Push(n) => {
                self.push(Some(*n)).map_err(|_| Error::MissingPush)?;
                self.cmds.push(c);
            }
            Cmd::Get(_) | Cmd::Const(_) => {
                self.push(None).map_err(|_| Error::MissingPush)?;
                self.cmds.push(c);
            }
            Cmd::StrLen => {
                self.pop(Some(ParamType::Str))?;
                self.push(None).map_err(|_| Error::MissingPush)?;
                self.cmds.push(c);
            }
            Cmd::Add
            | Cmd::Sub
            | Cmd::Mul
            | Cmd::Div
            | Cmd::Rem
            | Cmd::BitAnd
            | Cmd::BitOr
            | Cmd::BitXor
            | Cmd::Greater
            | Cmd::Less => {
                self.pop(Some(ParamType::Int))?;
                self.pop(Some(ParamType::Int))?;
                self.push(None).map_err(|_| Error::MissingPush)?;
                self.cmds.push(c);
            }
            Cmd::And | Cmd::Or | Cmd::Eq => {
                self.pop(None)?;
                self.pop(None)?;
                self.push(None).map_err(|_| Error::MissingPush)?;
                self.cmds.push(c);
            }
            Cmd::BitNot => {
                self.pop(Some(ParamType::Int))?;
                self.pop(None)?;
                self.cmds.push(c);
            }
            Cmd::Not => {
                self.pop(None)?;
                self.push(None).map_err(|_| Error::MissingPush)?;
                self.cmds.push(c);
            }
            Cmd::ANSIFix => {
                while self.sig.len() < 2 {
                    self.sig.push(None)
                }
                if let Some(ParamType::Str) = self.sig[0].replace(ParamType::Int) {
                    return Err(Error::ParamBothTypes(0));
                }
                if let Some(ParamType::Str) = self.sig[1].replace(ParamType::Int) {
                    return Err(Error::ParamBothTypes(1));
                }
                self.cmds.push(c);
            }
            Cmd::If => {
                self.start_if();
                self.cmds.push(c);
            }
            Cmd::Then => {
                self.pop(Some(ParamType::Int))?;
                self.then()?;
                self.cmds.push(c);
            }
            Cmd::Else => {
                self.els()?;
                self.cmds.push(c);
            }
            Cmd::Fi => {
                self.end_if()?;
                self.cmds.push(c);
            }
        }
        Ok(())
    }
}

/// `tparm!(format_string, ...)` formats `format_string` with the given parameters.
///
/// Returns a `Result<String,`[`binary_terminfo::format::Error`](format/enum.Error.html)`>`.
///
/// `format_string` is expected to be a `&str`, a `String`, or a `TerminfoString`.
///
/// Example
/// -------
/// ```
/// fn main() -> Result<(), binary_terminfo::format::Error> {
///     use binary_terminfo::*;
///     let comp = format::TerminfoString::from_string(
///         "%p1%d %?%p1%p2%=%t==%e%p1%p2%>%t>%e<%; %p2%d".into(),
///     )?;
///     assert_eq!(
///         tparm!(comp, 1, 3)?,
///         "1 < 3"
///     );
///     assert_eq!(
///         tparm!(comp, 1, 1)?,
///         "1 == 1"
///     );
///     assert_eq!(
///         tparm!(comp, 3, 1)?,
///         "3 > 1"
///     );
///
///     assert_eq!(
///         tparm!("The sum is %.3d.", 3 + 7 + -12 + -5)?,
///         "The sum is -007."
///     );
///     Ok(())
/// }
/// ```
#[macro_export]
macro_rules! tparm {
    ($s:expr$(, $arg:expr)*) => {
        $crate::format::AsTerminfoString::as_terminfo_string(&$s).map(|f| f.fmt(vec![$(&$arg),*])).unwrap_or_else(|e| Err(e))
    };
}
