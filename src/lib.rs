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
//! Lightweight reader and writer for ncurses binary terminfo format.
//!
//! Example
//! -------
//! ```rust, no_run
//! use binary_terminfo::*;
//! fn main() -> Result<(), std::io::Error> {
//!     let terminfo = Terminfo::default()?;
//!
//!     println!("{}",terminfo.get_str(StringCap::ClearScreen).unwrap_or("\x1b[H\x1b[J"));
//!
//!     Ok(())
//! }
//! ```
#[doc(hidden)]
pub mod caps;
pub mod format;
#[doc(hidden)]
pub mod terminfo;
#[doc(inline)]
pub use caps::{BooleanCap, IntegerCap, StringCap};
#[doc(inline)]
pub use format::TerminfoString;
#[doc(inline)]
pub use terminfo::Terminfo;

#[cfg(test)]
mod tests {
    macro_rules! concat_bytes {
        ($($x:expr),*$(,)?) => {
            {
                let mut v = Vec::new();
                $(v.extend($x.into_iter());)*
                v
            }
        };
    }
    use crate::*;
    #[test]
    fn editing() {
        let mut terminfo = Terminfo::new();

        terminfo.set_names(vec!["madeup", "madeup terminfo"]);
        terminfo.insert(BooleanCap::AutoRightMargin, true);
        terminfo.insert(IntegerCap::Lines, 24);
        terminfo.insert(StringCap::Bell, '\x07');
        terminfo.insert("also_madeup", true);
        terminfo.insert("another", false);
        terminfo.insert("another", true);
        terminfo.insert("one_more", 2);
        terminfo.insert("also_madeup", 3);

        let terminfo = terminfo.to_vec();
        assert_eq!(
            terminfo,
            concat_bytes! {
                b"\x1e\x02\x17\0\x02\0\x03\0\x02\0\x02\0",     // header
                b"madeup|madeup terminfo\0",                   // names
                b"\xFF\x01",                                   // bools
                b"\0",
                b"\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\x18\0\0\0", // ints
                b"\xFF\xFF\0\0",                               // str indices
                b"\x07\0",                                     // strs
                b"\x01\0\x02\0\0\0\x03\0\x1d\0",               // extended header
                b"\x01",                                       // bools,
                b"\0",
                b"\x02\0\0\0\x03\0\0\0",                       // ints
                b"",                                           // str indices
                b"\0\0\x08\0\x11\0",                           // key indices
                b"",                                           // strings
                b"another\0one_more\0also_madeup\0"            // keys
            }
        );

        let terminfo = Terminfo::from_vec(terminfo).unwrap();
        assert_eq!(terminfo.names(), &vec!["madeup", "madeup terminfo"]);
        assert_eq!(terminfo.get(BooleanCap::AutoRightMargin).unwrap(), &true);
        assert_eq!(terminfo.get(IntegerCap::Lines).unwrap(), &24);
        assert_eq!(terminfo.get("also_madeup").unwrap(), &3);
        assert_eq!(terminfo.get("another").unwrap(), &true);
    }
}
