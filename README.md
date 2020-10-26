rust-binary-terminfo
====================
Lightweight reader and writer for ncurses binary terminfo format.

Usage
-----
Add this to your `Cargo.toml`:
```toml
[dependencies]
binary_terminfo = { git = "https://github.com/emakman/rust-binary-terminfo" }
```

Example
-------
```rust
use binary_terminfo::*;

fn main() -> Result<(), std::io::Error> {
    let terminfo = Terminfo::default()?;

    if let Some(NumericValue(n)) = terminfo.get(NumericCap::Lines) {
        println!("Terminal has 24 lines.");
    }

    Ok(())
}
```

File Format
-----------
This is meant to be as straightforward an interface into terminfo as possible. It only reads the binary format described in the `term(5)` manpage distributed with `ncurses`, and not the berkely db format.

The `Terminfo` object can be converted to a `Vec<u8>`. This conversion uses the extended numeric format (i.e., 32-bit integers) and only uses the ncurses extended format if necessary (if there are no user caps, then there will be no extended header). Conversion to `Vec<u8>` is the only method provided for writing terminfo files.

The provided capabilities list is hardcoded and only covers the SVr4.1 caps and XSI extension caps. Unknown capabilities are dropped when the file is read (so in particular, if you read a file, and then write it, this may change the contents).
