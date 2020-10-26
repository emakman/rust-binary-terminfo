//! Private macros for creating simplistic regex-based tokenizers.
//!
//! This is more generic than it needs to be, but not enough so to be a waste of compile-time, and
//! it helps avoid unnecessary dependencies while leaving the code for the tokenizer (somewhat)
//! readable, at least, assuming we trust how this works.

/// The main usage is:
/// ```rust, no_compile
/// parse!(parse ($expr) or $Error {
///     $($rules)*
/// })
/// ```
/// The parser will call the rule named `__top__`, which must exist.
///
/// The returned value will be a `Result<Vec<$made>,$Error>` where `$made` is the output type of
/// the `__top__` rule.
macro_rules! parse {
    (parse ($s:expr) or $Error:ty {
        $(rule $rule:ident$( -> $made:ty )? {$($patterns:tt)*})*
    }) => {{
        $(rule!([$rule][$([$made])?[()]][$Error][$($patterns)*]);)*
        let mut _s: &str = ($s).as_ref();
        let mut _n: usize = 0;
        let mut _r = vec![];
        while let Some(_e) = __top__(&mut _s, &mut _n)? {
            _r.push(_e);
        }
        _r
    }};
}
/// Each rule generates a function, which, given a pointed string (i.e., a string and an index in
/// the string) produces a `Reault<Option<$made>,$Error>`. an `Ok(None)` indicates that there were
/// no more tokens in the string (this is the default return value), which is intentionally made
/// distinct from an error value.
///
/// A rule is of the form
/// ```rust, no_compile
///     rule $name $(-> $made)? {
///         $($patterns)*
///     }
/// ```
/// and generates a function (in the scope of the macro invocation)
/// `$name(&mut &str, &mut usize) -> Result<Option<$made>, $Error>`.
macro_rules! rule {
    ([$name:ident][[$made:ty]$([()])?][$Error:ty][$($patterns:tt)*]) => {
        #[allow(unreachable_patterns)]
        fn $name(_s: &mut &str, _n: &mut usize) -> Result<Option<$made>, $Error> {
            let _l = 0;
            patterns!([$($patterns)*][_s][_n][_c][_l][][]);
        }
    };
}
/// Each pattern gives a match pattern for matching a character or substring, and either the
/// corresponding `$made` value or subsequent patterns.
///
/// Some example patterns include:
///    * `[$pat] {$($subpat)*}` - match a character against the match pattern `$pat`, and,
///         if it matches, continue with the patterns `$($subpat)`.
///    * `[$pat] => {$made}` - match a character against the match pattern `$pat` and, and,
///         if it matches, return the value `$made`.
///    * `<$rule> {$($subpat)*}` - match the rule `$rule` and if a match is found, continue
///         with the patterns `$($subpat)`.
///    * `_ => {$made}` - match any character (not covered by another rule)
///         and return the value `$made`
///
/// If a `[$pat]` or `<$rule>` is followed with `+` then as many matches as possible are added to
/// the token. Similarly, `?` indicates that a match is optional (and we continue whether it is
/// found or not), while `*` means both that the match is optional and that as many matches as
/// possible should be included.
///
/// Rule matches, and repeated and optional patterns cannot bind variables so instead `as $name`
/// can be added. For example,
///    * `[$pat]+ as s` will bind `s` to a `Vec<char>` of matches.
///    * `<$rule>? as k` will bind `k` to an `Option<$made>` where `$made` is the output of rule
///      `$rule`.
///
/// The token as a whole can be bound like so:
///    * `[$pat] =>($tok) {$made}` will bind the matched token to `$tok`.
///
/// Any pattern can be preceded with `?=` to make it a look-ahead (that is, it makes sure that the
///     pattern would match, but does not include what was matched in the current match so far).
///
/// Some things which are known to be problems with this macro for more general use:
///    * rule matches take precedence over other matches, so, for example:
///         ```no_compile
///             __top__ -> bool {
///                 ['a']? {
///                     <maybe_n> => { false }
///                     ['l'] => { true }
///                 }
///             }
///             maybe_n -> () {
///                 ['n']? => {}
///             }
///         ```
///      will always return false (even when matching against "al") because the `<maybe_n>` is
///      copied to the top level (since `['a']?` is optional) and then takes precedence over
///      `['a']`. This problem is much less likely if rules are crafted to avoid matching the empty
///      string.
///    * There is no warning if a pattern is unused.
///    * Lookahead default patterns (i.e., ones beginning with `?=_` do not match at the end of the
///      string, and no rule has been provided for end-of-string matches.
macro_rules! patterns {
    // [pat] {...}
    ([ $(?=$(@$lookahead:meta)?)?[$($pat:tt)*] {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)*][$($parsed:tt)*]) => {
        patterns!([$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*
            [$($pat)*][{
                default!($($($lookahead)?[])?[*$idx += $len;]);
                patterns!([$($then)*][$str][$idx][$char][$len][][]);
            }]
        ]);
    };
    // [pat] => {...}
    ([ $(?=$(@$lookahead:meta)?)?[$($pat:tt)*] =>$(($tok:ident))? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)*][$($parsed:tt)*]) => {
        patterns!([$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*
            [$($pat)*][{
                default!($($($lookahead)?[])?[*$idx += $len;]);
                let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
                *$str = _l;
                *$idx = 0;
                return Ok(Some({$($then)*}))
            }]
        ]);
    };
    // [pat]? {...}
    ([ [$($pat:tt)*]?$( as $as:ident)? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)?][$($parsed:tt)*]) => {
        $(let mut $as = None;)?
        patterns!([$($then)*$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*
            [$($pat)*][{
                *$idx += $len;
                $($as = Some($char);)?
                patterns!([$($then)*][$str][$idx][$char][$len][][]);
            }]
        ]);
    };
    // [pat]? => {...}
    ([ [$($pat:tt)*]?$( as $as:ident)? =>$(($tok:ident))? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][][$($parsed:tt)*]) => {
        $(let mut $as = None;)?
        patterns!([$($after)*][$str][$idx][$char][$len][$($default)*
            {
                if let Some($char) = $str.split_at(*$idx).1.chars().next() {
                    let $len = $char.len_utf8();
                    match $char {
                        $($pat)* => {
                            $($as = Some($char);)?
                            *$idx += $len;
                        }
                        _ => {}
                    }
                }
                let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
                *$str = _l;
                *$idx = 0;
                return Ok(Some({$($then)*}))
            }
        ][$($parsed)*]);
    };
    // [pat]+ {...}
    ([ [$($pat:tt)*]+$( as $as:ident)? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)?][$($parsed:tt)*]) => {
        patterns!([$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*
            [$($pat)*][{
                $(let mut $as = vec![];)?
                while let Some($char) = $str.split_at(*$idx).1.chars().next() {
                    let $len = $char.len_utf8();
                    match $char {
                        $($pat)* => {
                            *$idx += $len;
                            $($as.push($char);)?
                        }
                        _ => { break }
                    }
                }
                patterns!([$($then)*][$str][$idx][$char][$len][][]);
            }]
        ]);
    };
    // [pat]+ => {...}
    ([ [$($pat:tt)*]+$( as $as:ident)? =>$(($tok:ident))? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)*][$($parsed:tt)*]) => {
        patterns!([$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*
            [$($pat)*][{
                $(let mut $as = vec![];)?
                while let Some($char) = $str.split_at(*$idx).1.chars().next() {
                    let $len = $char.len_utf8();
                    match $char {
                        $($pat)* => {
                            *$idx += $len;
                            $($as.push($char);)?
                        }
                        _ => { break }
                    }
                }
                let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
                *$str = _l;
                *$idx = 0;
                return Ok(Some({$($then)*}))
            }]
        ]);
    };
    // [pat]* {...}
    ([ [$($pat:tt)*]*$( as $as:ident)? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)?][$($parsed:tt)*]) => {
        $(let mut $as = vec![];)?
        patterns!([$($then)*$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*
            [$($pat)*][{
                while let Some($char) = $str.split_at(*$idx).1.chars().next() {
                    let $len = $char.len_utf8();
                    match $char {
                        $($pat)* => {
                            *$idx += $len;
                            $($as.push($char);)?
                        }
                        _ => { break }
                    }
                }
                patterns!([$($then)*][$str][$idx][$char][$len][][]);
            }]
        ]);
    };
    // [pat]* => {...}
    ([ [$($pat:tt)*]?$( as $as:ident)? =>$(($tok:ident))? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][][$($parsed:tt)*]) => {
        $(let mut $as = vec![];)?
        patterns!([$($after)*][$str][$idx][$char][$len][$($default)*
            {
                while let Some($char) = $str.split_at(*$idx).1.chars().next() {
                    let $len = $char.len_utf8();
                    match $char {
                        $($pat)* => {
                            *$idx += $len;
                            $($as.push($char);)?
                        }
                        _ => { break }
                    }
                }
                let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
                *$str = _l;
                *$idx = 0;
                return Ok(Some({$($then)*}))
            }
        ][$($parsed)*]);
    };
    // <f> {...}
    ([ $(?=$(@$lookahead:meta)?)?<$f:ident>$( as $as:ident)? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)*][$($parsed:tt)*]) => {
        let mut _idx = 0;
        let mut _str = $str.split_at(*$idx).1;
        if let Some(default!($([$as])?[_])) = $f(&mut _str, &mut _idx)? {
            default!($($($lookahead)?[])?[*$idx = $str.len() - _str.len();]);
            patterns!([$($then)*][$str][$idx][$char][$len][][]);
        } else {
            patterns!([$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*]);
        }
    };
    // <f> => {...}
    ([ $(?=$(@$lookahead:meta)?)?<$f:ident>$( as $as:ident)? =>$(($tok:ident))? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)*][$($parsed:tt)*]) => {
        let mut _idx = 0;
        let mut _str = $str.split_at(*$idx).1;
        if let Some(default!($([$as])?[_])) = $f(&mut _str, &mut _idx)? {
            default!($($($lookahead)?[])?[*$idx = $str.len() - _str.len();]);
            let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
            *$str = _l;
            *$idx = 0;
            return Ok(Some({$($then)*}))
        } else {
            patterns!([$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*]);
        }
    };
    // <f>? {...}
    ([ <$f:ident>?$( as $as:ident)? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)?][$($parsed:tt)*]) => {
        let mut _idx = 0;
        let mut _str = $str.split_at(*$idx).1;
        $(let mut $as = None;)?
        if let Some(_m) = $f(&mut _str, &mut _idx)? {
            $($as = Some(_m);)?
            *$idx = $str.len() - _str.len();
            patterns!([$($then)*][$str][$idx][$char][$len][][]);
        } else {
            patterns!([$($then)*$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*]);
        }
    };
    // <f>? => {...}
    ([ <$f:ident>?$( as $as:ident)? =>$(($tok:ident))? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][][$($parsed:tt)*]) => {
        let mut _idx = 0;
        let mut _str = $str.split_at(*$idx).1;
        $(let mut $as = None;)?
        if let Some(_m) = $f(&mut _str, &mut _idx)? {
            $($as = Some(_m);)?
            *$idx = $str.len() - _str.len();
            let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
            *$str = _l;
            *$idx = 0;
            return Ok(Some({$($then)*}))
        } else {
            patterns!([$($after)*][$str][$idx][$char][$len][{
                let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
                *$str = _l;
                *$idx = 0;
                return Ok(Some({$($then)*}))
            }][$($parsed)*]);
        }
    };
    // <f>+ {...}
    ([ <$f:ident>+$( as $as:ident)? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)?][$($parsed:tt)*]) => {
        let mut _idx = 0;
        let mut _str = $str.split_at(*$idx).1;
        if let Some(_m) = $f(&mut _str, &mut _idx)? {
            $(let mut $as = vec![_m];)?
            *$idx = $str.len() - _str.len();
            while let Some(_m) = $f(&mut _str, &mut _idx)? {
                $($as.push(_m);)?
                *$idx = $str.len() - _str.len();
            }
            patterns!([$($then)*][$str][$idx][$char][$len][][]);
        } else {
            patterns!([$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*]);
        }
    };
    // <f>+ => {...}
    ([ <$f:ident>+$( as $as:ident)? =>$(($tok:ident))? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)*][$($parsed:tt)*]) => {
        let mut _idx = 0;
        let mut _str = $str.split_at(*$idx).1;
        if let Some(_m) = $f(&mut _str, &mut _idx)? {
            $(let mut $as = vec![_m];)?
            *$idx = $str.len() - _str.len();
            while let Some(_m) = $f(&mut _str, &mut _idx)? {
                $($as.push(_m);)?
                *$idx = $str.len() - _str.len();
            }
            let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
            *$str = _l;
            *$idx = 0;
            return Ok(Some({$($then)*}))
        } else {
            patterns!([$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*]);
        }
    };
    // <f>* {...}
    ([ <$f:ident>*$( as $as:ident)? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][$($default:tt)?][$($parsed:tt)*]) => {
        let mut _idx = 0;
        let mut _str = $str.split_at(*$idx).1;
        $(let mut $as = vec![];)?
        if let Some(_m) = $f(&mut _str, &mut _idx)? {
            $($as.push(_m);)?
            *$idx = $str.len() - _str.len();
            while let Some(_m) = $f(&mut _str, &mut _idx)? {
                $($as.push(_m);)?
                *$idx = $str.len() - _str.len();
            }
            patterns!([$($then)*][$str][$idx][$char][$len][][]);
        } else {
            patterns!([$($then)*$($after)*][$str][$idx][$char][$len][$($default)*][$($parsed)*]);
        }
    };
    // <f>* => {...}
    ([ <$f:ident>*$( as $as:ident)? =>$(($tok:ident))? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][][$($parsed:tt)*]) => {
        let mut _idx = 0;
        let mut _str = $str.split_at(*$idx).1;
        $(let mut $as = vec![];)?
        if let Some(_m) = $f(&mut _str, &mut _idx)? {
            $($as.push(_m);)?
            *$idx = $str.len() - _str.len();
            while let Some(_m) = $f(&mut _str, &mut _idx)? {
                $($as.push(_m);)?
                *$idx = $str.len() - _str.len();
            }
            let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
            *$str = _l;
            *$idx = 0;
            return Ok(Some({$($then)*}))
        } else {
            patterns!([$($after)*][$str][$idx][$char][$len][{
                let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
                *$str = _l;
                *$idx = 0;
                return Ok(Some({$($then)*}))
            }][$($parsed)*]);
        }
    };
    // _ => {...}
    ([ $(?=$(@$lookahead:meta)?)?_ =>$(($tok:ident))? {$($then:tt)*}
     $($after:tt)*][$str:ident][$idx:ident][$char:ident][$len:ident][][$($parsed:tt)*]) => {
        patterns!([$($after)*][$str][$idx][$char][$len][
            default!($($($lookahead)?[])?[*$idx += $len;]);
            let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
            *$str = _l;
            *$idx = 0;
            return Ok(Some({$($then)*}))
        ][$($parsed)*]);
    };
    // .. => {...}
    ([ .. =>$(($tok:ident))? {$($else:tt)*}
     ][$str:ident][$idx:ident][$char:ident][$len:ident][][$([$($pat:tt)*][$($then:tt)*])+]) => {
        let _idx = *$idx;
        while let Some($char) = $str.split_at(*$idx).1.chars().next() {
            let $len = $char.len_utf8();
            match $char {
                $($($pat)* => {
                    if *$idx > _idx {
                        break;
                    } else {
                        $($then)*
                    }
                })*
                _ => { *$idx += $len; }
            }
        }
        if *$idx > _idx {
            let default!($([($tok,_l)])?[(_,_l)]) = $str.split_at(*$idx);
            *$str = _l;
            *$idx = 0;
            return Ok(Some({$($else)*}));
        } else {
            return Ok(None);
        }
    };
    // END
    ([][$str:ident][$idx:ident][$char:ident][$len:ident][$($($default:tt)+)?][$([$($pat:tt)*][$($then:tt)*])+]) => {
        while let Some($char) = $str.split_at(*$idx).1.chars().next() {
            let $len = $char.len_utf8();
            match $char {
                $($($pat)* => {$($then)*})*
                _ => { default!($([$($default)+])?[return Ok(None)]); }
            }
        }
        default!($([$($default)+])?[return Ok(None)]);
    };
    ([][$str:ident][$idx:ident][$char:ident][$len:ident][$($($default:tt)+)?][]) => {
        default!($([$($default)+])?[return Ok(None)]);
    };
}
macro_rules! default {
    ([$($d:tt)*]$($_:tt)?) => {$($d)*}
}
