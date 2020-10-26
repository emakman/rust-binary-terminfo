// Copyright ⓒ 2020 Tamvana Makuluni
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the “Software”), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//! The main `Terminfo` type.
use crate::caps::*;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fs::File;
use std::io::{Error, ErrorKind::*, Read, Seek, SeekFrom};
use Value::*;

/// A set of terminal capabilities.
///
/// The main use is to read terminfo for the current terminal:
/// ```rust, no_run
/// use binary_terminfo::*;
/// fn main() -> Result<(), std::io::Error> {
///     let terminfo = Terminfo::default()?;
///     
///     if let Some(bel) = terminfo.get_str("bel") {
///         print!("{}", bel);
///     }
///     if terminfo.get_bool(BooleanCap::BackColorErase).unwrap_or(false) {
///         println!("This terminal has the back color erase feature.")
///     }
///
///     Ok(())
/// }
/// ```
///
/// This object can also be converted to a Vec<u8> to write a new
/// terminfo file:
/// ```rust, no_run
/// use binary_terminfo::*;
/// use std::fs::OpenOptions;
/// use std::io::Write;
/// fn main() -> Result<(), std::io::Error> {
///     let mut terminfo = Terminfo::default()?;
///     terminfo.insert(IntegerCap::MaxColors, 256);
///     terminfo.insert(IntegerCap::MaxPairs, 65536);
///     //...
///
///     let mut f = OpenOptions::new()
///         .write(true)
///         .create_new(true)
///         .open("new_terminfo_file")?;
///     f.write(&terminfo.to_vec())?;
///
///     Ok(())
/// }
/// ```
///
/// Parameterized strings like SGR can be formatted using the [`tparm`](../format/macro.tparm.html) macro like so:
/// ```rust, no_run
/// use binary_terminfo::*;
/// fn main() -> Result<(), std::io::Error> {
///     let mut terminfo = Terminfo::default()?;
///     if let Some(sgr) = terminfo.get_str("sgr") {
///         if let Ok(underline) = tparm!(sgr, 0, 1, 0, 0, 0, 0, 0, 0, 0) {
///             if let Ok(clear) = tparm!(sgr, 0, 0, 0, 0, 0, 0, 0, 0, 0) {
///                 println!("{}underlined!{}", underline, clear);
///             }
///         }
///     }
///     Ok(())
/// }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Terminfo {
    names: Vec<String>,
    bools: Vec<(BooleanCap, Value)>,
    ints: Vec<(IntegerCap, Value)>,
    strs: Vec<(StringCap, Value)>,
    ex_bools: Vec<String>,
    ex_nums: Vec<String>,
    ex_strs: Vec<String>,
    ex: HashMap<String, Value>,
}
impl Terminfo {
    /// Creates a new completely empty terminfo.
    ///
    /// This is most useful if you are planning to write terminfo from
    /// scratch.
    pub fn new() -> Self {
        Terminfo {
            names: vec![],
            bools: vec![],
            ints: vec![],
            strs: vec![],
            ex_bools: vec![],
            ex_nums: vec![],
            ex_strs: vec![],
            ex: HashMap::new(),
        }
    }
    /// Convenience wrapper to load the terminfo for the current
    /// term. This simply calls [`for_term`](#method.for_term)
    /// with the contents of `$TERM`.
    pub fn default() -> Result<Self, Error> {
        if let Ok(term) = std::env::var("TERM") {
            Self::for_term(&term, None)
        } else {
            Err(NotFound.into())
        }
    }
    /// Load the terminfo for a specific terminal named `term`.
    /// `db` gives the name of a specific directory to use for the terminfo
    /// database.
    ///
    /// If `db` is `None`, then the following directories are searched:
    ///     1) either `$TERMINFO` or `$HOME/.terminfo`
    ///     2) the colon separated directories `$TERMINFO_DIRS` (in order).
    ///     3) `$PREFIX/usr/share/terminfo`
    pub fn for_term(term: &str, db: Option<&str>) -> Result<Self, Error> {
        match db {
            None => {
                // Search directories as described in
                // https://invisible-island.net/ncurses/man/terminfo.5.html
                if let Ok(dir) = std::env::var("TERMINFO") {
                    if let Ok(info) = Self::for_term(term, Some(&dir)) {
                        return Ok(info);
                    }
                } else {
                    if let Ok(home) = std::env::var("HOME") {
                        if let Ok(info) = Self::for_term(term, Some(&format!("{}/.terminfo", home)))
                        {
                            return Ok(info);
                        }
                    }
                }
                if let Ok(dirs) = std::env::var("TERMINFO_DIRS") {
                    let mut i = 0;
                    let mut j = 0;
                    while j <= dirs.len() {
                        if j == dirs.len() || dirs.as_bytes()[j] == b':' {
                            if let Ok(info) = Self::for_term(term, Some(&dirs[i..j])) {
                                return Ok(info);
                            }
                            i = j + 1;
                        }
                        j += 1;
                    }
                }
                if let Ok(info) = Self::for_term(
                    term,
                    Some(&format!(
                        "{}/usr/share/terminfo",
                        std::env::var("PREFIX").unwrap_or(String::from(""))
                    )),
                ) {
                    return Ok(info);
                }
                Err(NotFound.into())
            }
            Some(db) => {
                let t = term.chars().next().ok_or(Error::from(InvalidInput))?;
                Self::from_file(
                    File::open(format!("{}/{}/{}", db, t, term))
                        .or_else(|_| File::open(format!("{}/{:2x}/{}", db, t as u8, term)))?,
                )
            }
        }
    }
    /// Read terminfo from an already-open filehandle.
    pub fn from_file(mut f: std::fs::File) -> Result<Self, Error> {
        let mut data = vec![];
        f.seek(SeekFrom::Start(0))?;
        f.read_to_end(&mut data)?;
        Self::from_vec(data)
    }
    /// Read terminfo from the binary representation in memory.
    ///
    /// A round-trip from `Terminfo` to `Vec<u8>` should produce the
    /// same `Terminfo` object. However, unknown terminal capabilities
    /// are ignored (specifically, these should be mainly obsoleted
    /// capabilities), so data may be lost when reading the `Terminfo`
    /// in the first place.
    pub fn from_vec(data: Vec<u8>) -> Result<Self, Error> {
        macro_rules! read_blocks {
            ($i:ident => $b:block, $(|$({$d:tt})?)?$n:ident$($t:tt)*) => {
                let len = $b as usize;
                if $i.len() < len {
                    return Err(InvalidData.into());
                }
                let read_blocks!(@$n$($t)*) = $i.split_off(len);

                read_blocks!($(|$($d)?)?$n$($t)*);
            };
            ($(!)?$(|)?$i:ident $b:block) => {$b};
            (|$i:ident$($t:tt)+) => {
                if $i.len() > 0 {
                    read_blocks!($i$($t)*);
                } else {
                    read_blocks!(!$i$($t)*);
                }
            };
            (!$i:ident => $b:block, $(|)?$n:ident$($t:tt)*) => {
                #[allow(unused_variables)]
                let $n: Vec<u8> = Vec::with_capacity(0);
                read_blocks!(!$n$($t)*);
            };
            (@$n:ident $b:block) => {$n};
            (@$n:ident => $($t:tt)+) => {mut $n};
        }

        let mut header = data;

        let magic = &header[0..2];
        let legacy = magic == [0x1a, 0x1];
        if !(legacy || magic == [0x1e, 0x2]) {
            return Err(InvalidData.into());
        };

        read_blocks!(
            header => {12},
            names => {read_short(&header, 1)?.ok_or(Error::from(InvalidData))?},
            bools => {read_short(&header, 2)?.ok_or(Error::from(InvalidData))?},
            pad => {(names.len() + bools.len()) % 2},
            ints_raw => {read_short(&header, 3)?.ok_or(Error::from(InvalidData))? as usize * if legacy { 2 } else { 4 }},
            str_idx => {read_short(&header, 4)?.ok_or(Error::from(InvalidData))? as usize * 2},
            strs_raw => {read_short(&header, 5)?.ok_or(Error::from(InvalidData))? },
            |
            pad => {strs_raw.len() % 2},
            ex_header => {10},
            ex_bools_raw => {read_short(&ex_header, 0)?.ok_or(Error::from(InvalidData))?},
            pad => {ex_bools_raw.len() % 2},
            ex_nums_raw => {read_short(&ex_header, 1)?.ok_or(Error::from(InvalidData))? as usize * if legacy { 2 } else { 4 }},
            ex_str_idx => {read_short(&ex_header, 2)?.ok_or(Error::from(InvalidData))? as usize * 2},
            ex_bool_key_idx => {ex_bools_raw.len() * 2},
            ex_num_key_idx => {ex_nums_raw.len() / if legacy { 1 } else { 2 }},
            ex_str_key_idx => {
                           if 2 * ex_str_idx.len() + ex_num_key_idx.len() + ex_bool_key_idx.len() !=
                               (read_short(&ex_header, 3)?.ok_or(Error::from(InvalidData))? as usize * 2) {
                               return Err(InvalidData.into())
                           }
                           ex_str_idx.len()
                       },
            ex_strs_raw => {
                if ex_str_idx.len() == 0 { 0 }
                else {
                    let last_idx = read_short(&ex_str_idx, ex_str_idx.len()/2 - 1)?.ok_or(Error::from(InvalidData))? as usize;
                    let last = read_str(&ex_strs_raw, last_idx)?;
                    last_idx + last.len() + 1
                }
            },
            ex_keys_raw => {read_short(&ex_header, 4)?.ok_or(Error::from(InvalidData))? as usize - ex_strs_raw.len()},
            excess

            {
                if excess.len() != 0 {} // This check is ignored for now
                let names = read_str(&names, 0)?.split('|').map(|v| v.to_owned()).collect();

                let bools: Vec<_> = bools
                    .iter()
                    .enumerate()
                    .filter_map(|(k, &v)|
                        if (v as i8) < 0 {
                            None
                        } else {
                            BooleanCap::try_from(k)
                                .ok()
                                .map(|k| (k, BooleanValue(v==1)))
                        }
                    ).collect();

                let intc = ints_raw.len() / if legacy { 2 } else { 4 };
                let mut ints = Vec::with_capacity(intc);
                for k in 0..intc {
                    let v = if legacy { read_short(&ints_raw, k)?.map(|v| v as i32) } else { read_int(&ints_raw, k)? };
                    if let Some(v) = v {
                        if let Ok(k) = IntegerCap::try_from(k) {
                            ints.push((k, IntegerValue(v)));
                        }
                    }
                }

                let mut strs = Vec::with_capacity(str_idx.len() / 2);
                for k in 0..(str_idx.len() / 2) {
                    if let Some(v) = read_short(&str_idx, k)? {
                        let v = read_str(&strs_raw, v as usize)?;
                        if let Ok(k) = StringCap::try_from(k) {
                            strs.push((k, StringValue(v)))
                        }
                    }
                }

                let mut ex = HashMap::new();

                let mut ex_bools = Vec::with_capacity(ex_bools_raw.len());
                for k in 0..ex_bools_raw.len() {
                    let v = ex_bools_raw[k];
                    let k = read_str(&ex_keys_raw,
                        read_short(&ex_bool_key_idx, k)?.ok_or(Error::from(InvalidData))? as usize
                    )?;
                    if (v as i8) >= 0 {
                        ex_bools.push(k.clone());
                        ex.insert(
                            k,
                            BooleanValue(v==1)
                        );
                    }
                }

                let mut ex_nums = Vec::with_capacity(ex_num_key_idx.len() / 2);
                for k in 0..(ex_num_key_idx.len() / 2) {
                    let v = if legacy { read_short(&ex_nums_raw, k)?.map(|v| v as i32) } else { read_int(&ex_nums_raw, k)? };
                    let k = read_str(&ex_keys_raw,
                        read_short(&ex_num_key_idx, k)?.ok_or(Error::from(InvalidData))? as usize
                    )?;
                    if let Some(v) = v {
                        ex_nums.push(k.clone());
                        ex.insert(
                            k,
                            IntegerValue(v)
                        );
                    }
                }

                let mut ex_strs = Vec::with_capacity(ex_str_key_idx.len() / 2);
                for k in 0..(ex_str_key_idx.len() / 2) {
                    let v = read_str(&ex_strs_raw,
                        read_short(&ex_str_idx, k)?.ok_or(Error::from(InvalidData))? as usize
                    )?;
                    let k = read_str(&ex_keys_raw,
                        read_short(&ex_str_key_idx, k)?.ok_or(Error::from(InvalidData))? as usize
                    )?;
                    ex_strs.push(k.clone());
                    ex.insert(
                        k,
                        StringValue(v)
                    );
                }

                return Ok(Terminfo {
                    names,
                    bools,
                    ints,
                    strs,
                    ex_bools,
                    ex_nums,
                    ex_strs,
                    ex
                })
            }
        );
    }
    //
    /// The names of the terminal described by the terminfo.
    ///
    /// Example
    /// -------
    /// ```rust, no_run
    /// # use binary_terminfo::Terminfo;
    /// # fn main() -> Result<(), std::io::Error> {
    /// assert_eq!(
    ///     Terminfo::for_term("xterm-256color", None)?.names(),
    ///     &vec!["xterm-256color", "xterm with 256 colors"]
    /// );
    /// # Ok(())
    /// # }
    /// ```
    pub fn names(&self) -> &Vec<String> {
        &self.names
    }
    /// An iterator over the boolean capabilities (including extended capabilities)
    /// supported by the terminal.
    ///
    /// The following example produces `infocmp`-like output:
    /// ```rust, no_run
    /// use binary_terminfo::Terminfo;
    /// fn main() -> Result<(), std::io::Error> {
    ///     let terminfo = Terminfo::default()?;
    ///
    ///     for (k, v) in terminfo.bools() {
    ///         if v {
    ///             print!("{}, ", k.as_str());
    ///         }
    ///     }
    ///     print!("\n");
    ///
    ///     for (k, v) in terminfo.ints() {
    ///         print!("{}#{}, ", k.as_str(), v)
    ///     }
    ///     print!("\n");
    ///
    ///     for (k, v) in terminfo.strs() {
    ///         println!("{} = {:?}", k.as_str(), v);
    ///     }
    ///
    ///     Ok(())
    /// }
    /// ```
    pub fn bools(&self) -> impl Iterator<Item = (Key, bool)> + DoubleEndedIterator {
        self.bools
            .iter()
            .map(|(k, v)| (Key::BoolCap(*k), v.as_bool().copied().unwrap()))
            .chain(self.ex_bools.iter().map(move |k| {
                (
                    Key::Name(k),
                    self.ex.get(k).unwrap().as_bool().copied().unwrap(),
                )
            }))
    }
    /// An iterator over the integer capabilities (including extended capabilities)
    /// supported by the terminal.
    ///
    /// See [`bools`](#method.bools) for an example.
    pub fn ints(&self) -> impl Iterator<Item = (Key, i32)> + DoubleEndedIterator {
        self.ints
            .iter()
            .map(|(k, v)| (Key::IntCap(*k), v.as_int().copied().unwrap()))
            .chain(self.ex_nums.iter().map(move |k| {
                (
                    Key::Name(k),
                    self.ex.get(k).unwrap().as_int().copied().unwrap(),
                )
            }))
    }
    /// An iterator over the string capabilities (including extended capabilities)
    /// supported by the terminal.
    ///
    /// See [`bools`](#method.bools) for an example.
    pub fn strs(&self) -> impl Iterator<Item = (Key, &str)> + DoubleEndedIterator {
        self.strs
            .iter()
            .map(|(k, v)| (Key::StrCap(*k), v.as_str().unwrap()))
            .chain(
                self.ex_strs
                    .iter()
                    .map(move |k| (Key::Name(k), self.ex.get(k).unwrap().as_str().unwrap())),
            )
    }
    //
    /// Get the value of a specific capability.
    ///
    /// The key may be a capname (as a `&str`),
    ///     a [`BooleanCap`](../caps/enum.BooleanCap.html),
    ///     an [`IntegerCap`](../caps/enum.IntegerCap.html),
    ///     or a [`StringCap`](../caps/enum.BooleanCap.html)
    ///
    /// Examples
    /// --------
    /// ```rust, no_run
    /// use binary_terminfo::{Terminfo, terminfo::Value::*};
    /// # fn main() -> Result<(), std::io::Error> {
    /// let terminfo = Terminfo::default()?;
    /// if let Some(rgb) = terminfo.get("RGB") {
    ///     match rgb {
    ///         BooleanValue(_) => println!("Terminal provides a boolean RGB value.\n"),
    ///         IntegerValue(_) => println!("Terminal provides an integer RGB value.\n"),
    ///         StringValue(_) => println!("Terminal provides a string RGB value.\n"),
    ///     }
    /// }
    /// #     Ok(())
    /// # }
    /// ```
    pub fn get<'a, K: Into<Key<'a>>>(&self, k: K) -> Option<&Value> {
        match k.into() {
            Key::BoolCap(k) => self
                .bools
                .get(self.bools.binary_search_by_key(&&k, |(k, _)| k).ok()?)
                .map(|(_, v)| v),
            Key::IntCap(k) => self
                .ints
                .get(self.ints.binary_search_by_key(&&k, |(k, _)| k).ok()?)
                .map(|(_, v)| v),
            Key::StrCap(k) => self
                .strs
                .get(self.strs.binary_search_by_key(&&k, |(k, _)| k).ok()?)
                .map(|(_, v)| v),
            Key::Name(k) => {
                if let Some(v) = self.ex.get(k) {
                    Some(v)
                } else {
                    None
                }
            }
        }
    }
    //
    /// Get the value of a boolean capability.
    ///
    /// This is slightly faster for string keys than [`get`](#method.get) and it
    /// avoids needing to do extra work to determine the type of a value.
    ///
    /// If this key is not found, or an extended value is found with this key,
    /// but it is not a boolean, the return value will be `None`.
    pub fn get_bool<'a, K: Into<Key<'a>>>(&self, k: K) -> Option<bool> {
        match k.into() {
            Key::BoolCap(k) => self
                .bools
                .get(self.bools.binary_search_by_key(&&k, |(k, _)| k).ok()?)
                .map(|(_, v)| v.as_bool().copied())
                .flatten(),
            Key::Name(k) => {
                if let Some(v) = self.ex.get(k) {
                    Some(v.as_bool().copied()).flatten()
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    //
    /// Get the value of an integer capability.
    ///
    /// This is slightly faster for string keys than [`get`](#method.get) and it
    /// avoids needing to do extra work to determine the type of a value.
    ///
    /// If this key is not found, or an extended value is found with this key,
    /// but it is not an integer, the return value will be `None`.
    pub fn get_int<'a, K: Into<Key<'a>>>(&self, k: K) -> Option<i32> {
        match k.into() {
            Key::IntCap(k) => self
                .ints
                .get(self.ints.binary_search_by_key(&&k, |(k, _)| k).ok()?)
                .map(|(_, v)| v.as_int().copied())
                .flatten(),
            Key::Name(k) => {
                if let Some(v) = self.ex.get(k) {
                    Some(v.as_int().copied()).flatten()
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    //
    /// Get the value of a string capability.
    ///
    /// This is slightly faster for string keys than [`get`](#method.get) and it
    /// avoids needing to do extra work to determine the type of a value.
    ///
    /// If this key is not found, or an extended value is found with this key,
    /// but it is not an string, the return value will be `None`.
    pub fn get_str<'a, K: Into<Key<'a>>>(&self, k: K) -> Option<&str> {
        match k.into() {
            Key::StrCap(k) => self
                .strs
                .get(self.strs.binary_search_by_key(&&k, |(k, _)| k).ok()?)
                .map(|(_, v)| v.as_str())
                .flatten(),
            Key::Name(k) => {
                if let Some(v) = self.ex.get(k) {
                    Some(v.as_str()).flatten()
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    //
    /// Set the list of names for the terminal.
    pub fn set_names<I: ToString>(&mut self, names: Vec<I>) {
        self.names = names.into_iter().map(|name| name.to_string()).collect();
    }
    /// Insert or replace a value into the terminfo.
    ///
    /// Returns the value that was replaced or `None` if inserting a new value.
    ///
    /// The key may be a capname (as a `&str`),
    ///     a [`BooleanCap`](../caps/enum.BooleanCap.html),
    ///     an [`IntegerCap`](../caps/enum.IntegerCap.html),
    ///     or a [`StringCap`](../caps/enum.BooleanCap.html).
    ///
    /// If the key is a `&str`, the function first attempts to convert it to
    ///     another type of key by interpreting it as a capcode or a capname.
    /// Only if the key does not match a known capcode or capname will it be
    ///     interpreted as an extended key.
    ///
    /// The value may be a `bool`, `i32`, `&str`, or `String`. If the key is,
    ///     for example, a `BooleanCap` and the value is not a `bool`, then
    ///     no value will be inserted, but no error will be produced.
    /// It is therefore best practice to use strings as keys only when the
    ///     key being inserted is an extended capability, or to check
    ///     the key type by converting to a `Key` before inserting.
    pub fn insert<'a, K: Into<Key<'a>>, V: Into<Value>>(&mut self, k: K, v: V) -> Option<Value> {
        match k.into() {
            Key::BoolCap(k) => {
                if let mut v @ BooleanValue(_) = v.into() {
                    match self.bools.binary_search_by_key(&&k, |(k, _)| k) {
                        Ok(i) => {
                            std::mem::swap(&mut self.bools[i].1, &mut v);
                            Some(v)
                        }
                        Err(i) => {
                            self.bools.insert(i, (k, v));
                            None
                        }
                    }
                } else {
                    None
                }
            }
            Key::IntCap(k) => {
                if let mut v @ IntegerValue(_) = v.into() {
                    match self.ints.binary_search_by_key(&&k, |(k, _)| k) {
                        Ok(i) => {
                            std::mem::swap(&mut self.ints[i].1, &mut v);
                            Some(v)
                        }
                        Err(i) => {
                            self.ints.insert(i, (k, v));
                            None
                        }
                    }
                } else {
                    None
                }
            }
            Key::StrCap(k) => {
                if let mut v @ StringValue(_) = v.into() {
                    match self.strs.binary_search_by_key(&&k, |(k, _)| k) {
                        Ok(i) => {
                            std::mem::swap(&mut self.strs[i].1, &mut v);
                            Some(v)
                        }
                        Err(i) => {
                            self.strs.insert(i, (k, v));
                            None
                        }
                    }
                } else {
                    None
                }
            }
            Key::Name(k) => match (self.ex.get(k), v.into()) {
                (Some(BooleanValue(_)), v @ BooleanValue(_))
                | (Some(IntegerValue(_)), v @ IntegerValue(_))
                | (Some(StringValue(_)), v @ StringValue(_)) => self.ex.insert(k.to_owned(), v),
                (Some(BooleanValue(_)), v) => {
                    if let Some((i, _)) = self.ex_bools.iter().enumerate().find(|(_, ek)| ek == &k)
                    {
                        self.ex_bools.remove(i);
                    }
                    let r = self.ex.remove(k);
                    self.insert(k, v);
                    r
                }
                (Some(IntegerValue(_)), v) => {
                    if let Some((i, _)) = self.ex_nums.iter().enumerate().find(|(_, ek)| ek == &k) {
                        self.ex_nums.remove(i);
                    }
                    let r = self.ex.remove(k);
                    self.insert(k, v);
                    r
                }
                (Some(StringValue(_)), v) => {
                    if let Some((i, _)) = self.ex_strs.iter().enumerate().find(|(_, ek)| ek == &k) {
                        self.ex_strs.remove(i);
                    }
                    let r = self.ex.remove(k);
                    self.insert(k, v);
                    r
                }
                (None, v @ BooleanValue(_)) => {
                    self.ex_bools.push(k.to_owned());
                    self.ex.insert(k.to_owned(), v);
                    None
                }
                (None, v @ IntegerValue(_)) => {
                    self.ex_nums.push(k.to_owned());
                    self.ex.insert(k.to_owned(), v);
                    None
                }
                (None, v @ StringValue(_)) => {
                    self.ex_strs.push(k.to_owned());
                    self.ex.insert(k.to_owned(), v);
                    None
                }
            },
        }
    }
    /// Remove a value from the terminfo struct.
    ///
    /// Returns the value that was removed, or `None` if the key wasn't found.
    pub fn remove<'a, K: Into<Key<'a>>>(&mut self, k: K) -> Option<Value> {
        match k.into() {
            Key::BoolCap(k) => {
                if let Some((i, _)) = self.bools.iter().enumerate().find(|(_, (b, _))| b == &k) {
                    Some(self.bools.remove(i).1)
                } else {
                    None
                }
            }
            Key::IntCap(k) => {
                if let Some((i, _)) = self.ints.iter().enumerate().find(|(_, (b, _))| b == &k) {
                    Some(self.ints.remove(i).1)
                } else {
                    None
                }
            }
            Key::StrCap(k) => {
                if let Some((i, _)) = self.strs.iter().enumerate().find(|(_, (b, _))| b == &k) {
                    Some(self.strs.remove(i).1)
                } else {
                    None
                }
            }
            Key::Name(k) => match self.ex.remove(k) {
                v @ Some(BooleanValue(_)) => {
                    if let Some((i, _)) = self.ex_bools.iter().enumerate().find(|(_, ek)| ek == &k)
                    {
                        self.ex_bools.remove(i);
                    }
                    v
                }
                v @ Some(IntegerValue(_)) => {
                    if let Some((i, _)) = self.ex_nums.iter().enumerate().find(|(_, ek)| ek == &k) {
                        self.ex_nums.remove(i);
                    }
                    v
                }
                v @ Some(StringValue(_)) => {
                    if let Some((i, _)) = self.ex_strs.iter().enumerate().find(|(_, ek)| ek == &k) {
                        self.ex_strs.remove(i);
                    }
                    v
                }
                _ => None,
            },
        }
    }
    /// Convert the terminfo struct back to the binary format of an
    /// ncurses-compatible terminfo file.
    ///
    /// This can be used to write a terminfo file as in the example [`above`](#).
    pub fn to_vec(self) -> Vec<u8> {
        let mut r = vec![];
        let mut stri = vec![];
        let mut strs = vec![];

        let mut i = 0;
        for (k, v) in self.strs.iter() {
            while i < *k as usize {
                write_str(&mut stri, &mut strs, None);
                i += 1;
            }
            write_str(&mut stri, &mut strs, v.as_str());
            i += 1;
        }

        // Magic number
        r.push(0x1e);
        r.push(0x2);
        write_short(
            &mut r,
            Some(self.names.iter().fold(0, |s, n| s + n.len() + 1) as i16),
        );
        write_short(
            &mut r,
            Some(self.bools.last().map(|(k, _)| *k as usize + 1).unwrap_or(0) as i16),
        );
        write_short(
            &mut r,
            Some(self.ints.last().map(|(k, _)| *k as usize + 1).unwrap_or(0) as i16),
        );
        write_short(&mut r, Some((stri.len() / 2) as i16));
        write_short(&mut r, Some(strs.len() as i16));

        let mut first = true;
        for name in self.names {
            if first {
                first = false
            } else {
                r.push(b'|')
            }
            r.extend(name.as_bytes());
        }
        r.push(0);

        i = 0;
        for (k, v) in self.bools {
            while i < k as usize {
                r.push(0xFF);
                i += 1;
            }
            r.push(v.as_bool().map(|v| *v as u8).unwrap_or(0xFF));
            i += 1;
        }

        if r.len() % 2 == 1 {
            r.push(0)
        }

        i = 0;
        for (k, v) in self.ints {
            while i < k as usize {
                write_int(&mut r, None);
                i += 1;
            }
            write_int(&mut r, v.as_int().copied());
            i += 1;
        }

        r.append(&mut stri);
        r.append(&mut strs);

        let mut ex_bools = vec![];
        let mut ex_nums = vec![];
        let mut ex_stri = vec![];
        let mut ex_strs = vec![];
        let mut ex_keyi = vec![];
        let mut ex_keys = vec![];
        for k in self.ex_bools {
            if let Some(v) = self.ex.get(&k) {
                if let Some(&v) = v.as_bool() {
                    ex_bools.push(v as u8);
                    write_str(&mut ex_keyi, &mut ex_keys, Some(&k))
                }
            }
        }
        for k in self.ex_nums {
            if let Some(v) = self.ex.get(&k) {
                if let Some(&v) = v.as_int() {
                    write_int(&mut ex_nums, Some(v));
                    write_str(&mut ex_keyi, &mut ex_keys, Some(&k))
                }
            }
        }
        for k in self.ex_strs {
            if let Some(v) = self.ex.get(&k) {
                if let Some(v) = v.as_str() {
                    write_str(&mut ex_stri, &mut ex_strs, Some(v));
                    write_str(&mut ex_keyi, &mut ex_keys, Some(&k))
                }
            }
        }
        if ex_keyi.len() > 0 {
            if r.len() % 2 == 1 {
                r.push(0)
            }

            write_short(&mut r, Some(ex_bools.len() as i16));
            write_short(&mut r, Some((ex_nums.len() / 4) as i16));
            write_short(&mut r, Some((ex_stri.len() / 2) as i16));
            write_short(&mut r, Some(((ex_stri.len() + ex_keyi.len()) / 2) as i16));
            write_short(&mut r, Some((ex_strs.len() + ex_keys.len()) as i16));

            r.extend(ex_bools);
            if r.len() % 2 == 1 {
                r.push(0)
            }
            r.extend(ex_nums);
            r.extend(ex_stri);
            r.extend(ex_keyi);
            r.extend(ex_strs);
            r.extend(ex_keys);
        }

        r
    }
}

#[inline]
fn read_short(a: &[u8], i: usize) -> Result<Option<i16>, Error> {
    let v = (a.get(2 * i).copied().ok_or(Error::from(InvalidData))? as u16
        + ((a.get(2 * i + 1).copied().ok_or(Error::from(InvalidData))? as u16) << 8))
        as i16;
    if v < 0 {
        Ok(None)
    } else {
        Ok(Some(v))
    }
}
#[inline]
fn read_int(a: &[u8], i: usize) -> Result<Option<i32>, Error> {
    let v = (a.get(4 * i).copied().ok_or(Error::from(InvalidData))? as u32
        + ((a.get(4 * i + 1).copied().ok_or(Error::from(InvalidData))? as u32) << 8)
        + ((a.get(4 * i + 2).copied().ok_or(Error::from(InvalidData))? as u32) << 16)
        + ((a.get(4 * i + 3).copied().ok_or(Error::from(InvalidData))? as u32) << 24))
        as i32;
    if v < 0 {
        Ok(None)
    } else {
        Ok(Some(v))
    }
}
#[inline]
fn read_str(a: &[u8], start: usize) -> Result<String, Error> {
    let mut end = start;
    while end < a.len() && a[end] != 0 {
        end += 1;
    }
    if end == a.len() {
        Err(Error::from(InvalidData))
    } else {
        Ok(unsafe { std::str::from_utf8_unchecked(&a[start..end]) }.to_owned())
    }
}

#[inline]
fn write_short(a: &mut Vec<u8>, i: Option<i16>) {
    let mut i = i.unwrap_or(-1) as u16;
    a.push((i % 256) as u8);
    i >>= 8;
    a.push((i % 256) as u8);
}

#[inline]
fn write_int(a: &mut Vec<u8>, i: Option<i32>) {
    let mut i = i.unwrap_or(-1) as u32;
    a.push((i % 256) as u8);
    i >>= 8;
    a.push((i % 256) as u8);
    i >>= 8;
    a.push((i % 256) as u8);
    i >>= 8;
    a.push((i % 256) as u8);
}

#[inline]
fn write_str(a: &mut Vec<u8>, b: &mut Vec<u8>, s: Option<&str>) {
    if let Some(s) = s {
        write_short(a, Some(b.len() as i16));
        b.extend(s.as_bytes());
        b.push(0)
    } else {
        write_short(a, None)
    }
}

/// Possible Key types for a terminfo capability.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Key<'a> {
    BoolCap(BooleanCap),
    IntCap(IntegerCap),
    StrCap(StringCap),
    Name(&'a str),
}
impl<'a> From<BooleanCap> for Key<'a> {
    fn from(c: BooleanCap) -> Key<'a> {
        Key::BoolCap(c)
    }
}
impl<'a> From<IntegerCap> for Key<'a> {
    fn from(c: IntegerCap) -> Key<'a> {
        Key::IntCap(c)
    }
}
impl<'a> From<StringCap> for Key<'a> {
    fn from(c: StringCap) -> Key<'a> {
        Key::StrCap(c)
    }
}
/// When converting a `&str` to a `Key`, we first try
/// to interpret the string as capname, then as a capcode.
///
/// In both cases, it searches for a StringCap, then an IntegerCap,
/// then a BooleanCap and stops with the first match it finds.
///
/// In particular, note that, the string "ML" is interpreted as
/// `StringCap::SetLeftMargin` rather than `StringCap::SetLrMargin`.
impl<'a> From<&'a str> for Key<'a> {
    fn from(s: &'a str) -> Key<'a> {
        if let Some(s) = StringCap::from_capname(s) {
            Self::StrCap(s)
        } else if let Some(s) = IntegerCap::from_capname(s) {
            Self::IntCap(s)
        } else if let Some(s) = BooleanCap::from_capname(s) {
            Self::BoolCap(s)
        } else if let Some(s) = StringCap::from_capcode(s) {
            Self::StrCap(s)
        } else if let Some(s) = IntegerCap::from_capcode(s) {
            Self::IntCap(s)
        } else if let Some(s) = BooleanCap::from_capcode(s) {
            Self::BoolCap(s)
        } else {
            Key::Name(s)
        }
    }
}
impl<'a> Key<'a> {
    /// Returns the capname for a key (or the key itself if the key is a `&str`).
    ///
    /// The documentation for [`Terminfo`](struct.Terminfo.html#method.bools) gives an example.
    pub fn as_str(&self) -> &'a str {
        match self {
            Key::BoolCap(c) => c.capname(),
            Key::IntCap(c) => c.capname(),
            Key::StrCap(c) => c.capname(),
            Key::Name(s) => s,
        }
    }
}

/// The type of a terminfo value.
///
/// This value is only returned by the [`get`](struct.Terminfo.html#method.get)
/// method on the [`Terminfo`](struct.Terminfo.html) struct. Since one generally
/// knows the type of a capability when looking it up, it is mostly preferable
/// to avoid interacting with this type directly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    BooleanValue(bool),
    IntegerValue(i32),
    StringValue(String),
}
impl Value {
    pub fn is_bool(&self) -> bool {
        if let BooleanValue(_) = self {
            true
        } else {
            false
        }
    }
    pub fn is_num(&self) -> bool {
        if let IntegerValue(_) = self {
            true
        } else {
            false
        }
    }
    pub fn is_str(&self) -> bool {
        if let StringValue(_) = self {
            true
        } else {
            false
        }
    }
    pub fn as_bool(&self) -> Option<&bool> {
        if let BooleanValue(b) = self {
            Some(&b)
        } else {
            None
        }
    }
    pub fn as_int(&self) -> Option<&i32> {
        if let IntegerValue(n) = self {
            Some(&n)
        } else {
            None
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        if let StringValue(s) = self {
            Some(&s)
        } else {
            None
        }
    }
}
impl From<bool> for Value {
    fn from(v: bool) -> Value {
        BooleanValue(v)
    }
}
impl From<i32> for Value {
    fn from(v: i32) -> Value {
        IntegerValue(v)
    }
}
impl From<String> for Value {
    fn from(v: String) -> Value {
        StringValue(v)
    }
}
impl From<&str> for Value {
    fn from(v: &str) -> Value {
        StringValue(v.to_owned())
    }
}
impl From<char> for Value {
    fn from(v: char) -> Value {
        StringValue(v.to_string())
    }
}
impl std::cmp::PartialEq<bool> for Value {
    fn eq(&self, o: &bool) -> bool {
        self == &BooleanValue(*o)
    }
}
impl std::cmp::PartialEq<i32> for Value {
    fn eq(&self, o: &i32) -> bool {
        self == &IntegerValue(*o)
    }
}
impl std::cmp::PartialEq<&str> for Value {
    fn eq(&self, o: &&str) -> bool {
        if let StringValue(s) = self {
            s == o
        } else {
            false
        }
    }
}
impl std::cmp::PartialOrd<i32> for Value {
    fn partial_cmp(&self, o: &i32) -> Option<std::cmp::Ordering> {
        if let IntegerValue(s) = self {
            Some(s.cmp(o))
        } else {
            None
        }
    }
}
