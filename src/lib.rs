//! # KeyTree
//! 
//! `KeyTree` is a text format designed to convert human readable information into Rust
//! data-structures.
//!
//! # Mini-Tutorial
//! 
//! Lets say we have a struct like
//! ```
//! struct Hobbit {
//!     name: String,
//!     age: u32,
//!     friends: Vec<Hobbit>,
//!     nick: Option<String>,
//! }
//! ```
//! and we want to record in a file how to create an instance of this struct. So we create a string
//! like
//! ```text
//! hobbit:
//!     name:         Frodo Baggins
//!     age:          60
//!     friends:
//!         hobbit:
//!             name: Bilbo Baggins
//!             age:  111
//!         hobbit:
//!             name: Samwise Gamgee
//!             age:  38
//!             nick: Sam
//! ```
//! Now we need to tell the struct how to select the the relevant part of this string, so for
//! instance we need to tell the struct that we get the name by following the path 
//! `hobbit::name`. This selection mechanism has to be somewhat more sophisticated because we want
//! to be able to select a `Vec` by, for instance, using the `hobbit::friends::hobbit` path to
//! select both of Frodo's friends. Once we have selected the set of lines in the string we need a
//! way to tell the data-structure how to convert that line into the correct type for the
//! data-structure. To do this we need to implement the `FromStr` trait (if the field type does not
//! already implement one) for the, so that the data-structure can take the selected key-values, and
//! convert them to the field type. If the field type is a type `T` that we have built, we can
//! implement `TryInto<T>` on it. The ! `TryInto` implementation for `Hobbit` looks like
//! ``` 
//! impl<'a> TryInto<Hobbit> for KeyTreeRef<'a> {
//!     type Error = Error;
//! 
//!     fn try_into(self) -> Result<Hobbit, Error> {
//!         Ok(
//!             Hobbit {
//!                 name:       self.value("hobbit::name")?,
//!                 age:        self.value("hobbit::age")?,
//!                 friends:    self.opt_vec_at("hobbit::friends::hobbit")?,
//!                 nick:       self.opt_value("hobbit::nick")?,
//!             }
//!         )
//!     }
//! }
//! ```
//! The important functions are
//! ```
//! self.value("a::b::c")?
//! ```
//! and  which converts from a string and
//! ```
//! self.at("a::b::c")?
//! ```
//! which converts to a type `T` implementing the `TryInto<T>` trait. Then there are variations of
//! `value()` and `at()` for handling conversions into `Options`:
//!
//! ```
//! self.opt_value("a::b::c")?
//! ```
//! and
//! ```
//! self.opt_at("a::b::c")
//! ```
//! In these cases, if the selected key-value does not exist, we get a `None` value. To convert into
//! a `Vec` we can use
//! ```
//! self.vec_value("a::b::c")?
//! ```
//! and
//! ```
//! self.vec_at("a::b::c")?
//! ```
//! which require at least one key-value and 
//! ```
//! self.opt_vec_at("a::b::c")?
//! ```
//! and
//! ```
//! self.opt_vec_value("a::b::c")?
//! ```
//! which will return an empty `Vec` if the key-value does not exist.
//! 
//! ## Example
//! 
//! `Into` from `KeyTree` into Rust types is automatically implemented for `Vec<T>`, `Option<T>`
//! and basic Rust types. `KeyTree` text can be automatically converted to these data types, making
//! use of type inference. The `at()` function returns an iterator over `KeyTree` types that can be
//! used to implement `Into` for your own types. The following example should cover 90 percent of
//! use cases,
//! 
//! ```rust
//! use std::convert::TryInto;
//! use keytree::{KeyTree, KeyTreeRef};
//! use keytree::Error;
//! 
//! static HOBBITS: &'static str = r#"
//! hobbit:
//!     name:         Frodo Baggins
//!     age:          60
//!     friends:
//!         hobbit:
//!             name: Bilbo Baggins
//!             age:  111
//!         hobbit:
//!             name: Samwise Gamgee
//!             age:  38
//!             nick: Sam
//! "#;
//! 
//! #[derive(Debug)]
//! struct Hobbit {
//!     name: String,
//!     age: u32,
//!     friends: Vec<Hobbit>,
//!     nick: Option<String>,
//! }
//! 
//! impl<'a> TryInto<Hobbit> for KeyTreeRef<'a> {
//!     type Error = Error;
//! 
//!     fn try_into(self) -> Result<Hobbit, Error> {
//!         Ok(
//!             Hobbit {
//!                 name:       self.value("hobbit::name")?,
//!                 age:        self.value("hobbit::age")?,
//!                 friends:    self.vec_at("hobbit::friends::hobbit")?,
//!                 nick:       self.opt_value("hobbit::nick")?,
//!             }
//!         )
//!     }
//! }
//! 
//! fn main() {
//!     let kt = KeyTree::parse(HOBBITS).unwrap();
//!     let hobbit: Hobbit = kt.to_ref().try_into().unwrap();
//! 
//!     &dbg!(&hobbit);
//! }
//! ```
//!
//! ## Data Specification 
//! 
//! - Indentation has meaning and is 4 spaces, relative to the top key. Since indenting is
//!    relative to the top key, then you can neatly align strings embedded in code.
//! 
//! - Each line can be empty, have whitespace only, be a comment, be a key, or be a key/value
//!    pair.
//! 
//! - There are keys and values. Key/Value pairs look like
//! 
//! ```text
//! name: Frodo
//! ```
//! are used for `struct` fields and `enum` variants.
//! 
//! Keys refer to child keys or child key/value pairs indented on lines under it, for example
//! 
//! ```text
//! hobbit:
//!     name: Frodo
//! ```
//! hobbit refers to the name of the struct or enum. In this way, the data maps simply to Rust
//! data-structures.
//! 
//! - If a key has many children with the same key, it forms a collection, for example
//! 
//! ```test
//! hobbit:
//!     name: Frodo
//!     name: Bilbo
//! ```
//! is a collection of hobbits.
//! 
//! - Keys must not include but must be followed by a colon `:`.
//! 
//! - Values are all characters between the combination of ':' and whitespace and the end of the
//!    line. The value is trimmed of whitespace at both ends.
//! 
//! - A comment line starts witha any amount of whitespace followed by `//`. 
//! 
//! ```text
//! // comment
//! hobbit:
//!     // another comment
//!     name: Frodo
//! ```
//! ## Efficiency
//!
//! There are no copies of the original string. The parsing process builds of immutable tree-structure which
//! points into the original string. Selection operations involve the manipulation of a single `usize`
//! cursor, so once A `KeyTree` is built, many lightweight `KeyTree` refs can be efficiently built
//! and used for searching. So the only string copy that occurs is the final conversion into the
//! receiving data-structure. Following a path into a keytree involves a scan of differently named
//! siblings held in a Vec. The assumption is that the number of different sibling names is
//! generally small because the number of fields in data-structures is also generally small. From
//! the point of view of compile time, there are no dependencies and no macros.

#![forbid(unsafe_code)]

use std::convert::TryInto;
use std::fmt;
use std::fmt::Display;
use std::str::FromStr;

pub use crate::error::Error;
use crate::error::*;
use crate::parser::Builder;

mod builder;
pub mod error;
pub(crate) mod parser;
pub mod serialize;

type Result<T> = std::result::Result<T, Error>;

// A `KeyPath` is used to follow keys into a keytree. Think of `KeyPath` as an iterator with a
// double window looking into a (parent segment, child segment).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub (crate) struct KeyPath {
    segments: Vec<String>,
    counter: usize,
}

impl KeyPath {

    pub (crate) fn is_last(&self) -> bool {
        self.counter == self.segments.len() - 2
    }

    pub (crate) fn advance(&mut self) {
        self.counter += 1;
        if self.counter >= self.segments.len() {
            println!("Keypath has exceeded end.");
            panic!()
        };
    }

    pub (crate) fn parent_segment(&self) -> String {
        self.segments[self.counter].clone()
    }

    pub (crate) fn child_segment(&self) -> String {
        self.segments[self.counter + 1].clone()
    }

    pub (crate) fn from_str(s: &str) -> Self {
        let v = s.split(':')
            .filter(|s| !s.is_empty())
            .map(|s| String::from(s))
            .collect::<Vec<String>>();
        KeyPath {
            segments: v,
            counter: 0,
        }
    }
}

impl Display for KeyPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        for segment in &self.segments {
            s.push_str(&segment);
            s.push_str("::");
        }
        s.pop();
        s.pop();
        write!(f, "{}", s)
    }
}

// A Token represents a parsed line of a keytree string. It contains a pointer to its `next`
// sibling. A `KeyValue` token contains a `Vec` of its children, the first value of the tuple is
// the child token's key. The second value is the tokens index in the `KeyTree` struct. The `line`
// field locates the error in the original keytree string and is passed on to errors.
#[derive(Clone, Debug)]
pub(crate) enum Token<'a> {
    Key {
        key:        &'a str,
        children:   Vec<(&'a str, usize)>,
        next:       Option<usize>,
        line:       usize, 
    },
    KeyValue {
        key:        &'a str,
        value:      &'a str,
        next:       Option<usize>,
        line:       usize,
    },
}

impl<'a> Token<'a> {

    pub fn line(&self) -> usize {
        match self {
            Token::Key { line, .. } => *line,
            Token::KeyValue { line, .. } => *line,
        }
    }

    pub fn key(&self) -> &'a str {
        match self {
            Token::Key {key, ..} => key,
            Token::KeyValue {key, ..} => key,
        }
    }

    // Will panic if called on a Token::Key. Always check before invoking this function.
    pub fn value(&self) -> &'a str {
        match self {
            Token::Key {..} => panic!(),
            Token::KeyValue { value, ..} => value,
        }
    }

    pub fn next(&self) -> Option<usize> {
        match self {
            Token::Key { next, .. } => *next,
            Token::KeyValue { next, .. } => *next,
        }
    }

    // Used for building the parsed keytree. Set the next iteration of the Token to a token with
    // index token_i.
    pub fn set_next(&mut self, token_i: usize) {
        match self {
            Token::KeyValue {ref mut next, ..  } => {
                *next = Some(token_i);
            },
            Token::Key {ref mut next, .. } => {
                *next = Some(token_i);
            },
        }
    }

    // Used for building the parsed keytree.
    pub fn set_child(&mut self, key: &'a str, child_ix: usize) {
        match self {
            Token::Key { children, .. } => {
                children.push((key, child_ix))
            },
            Token::KeyValue {..} => { panic!() },
        }
    }
}

impl<'a> fmt::Display for Token<'a> {
   fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Key { key, .. } => write!(f, "{}:", key),
            Token::KeyValue { key, value, .. } => {
                write!(f, "{}: {}", key, value)
            },
        }
    }
}

/// The parsed keytree string.
#[derive(Debug)]
pub struct KeyTree<'a> {
    s:      &'a str,
    tokens: Vec<Token<'a>>,
}

impl<'a> KeyTree<'a> {

    /// Returns a lightweight reference to the root of `KeyTree`.
    pub fn to_ref(&'a self) -> KeyTreeRef<'a> {
        KeyTreeRef(self, 0)
    }

    /// Parse the keytree string.
    pub fn parse(s: &'a str) -> Result<Self> {
        Builder::parse(s)
    }

    pub (crate) fn siblings(&self, index: usize) -> Vec<usize> {
        let token = self.tokens[index].clone();
        
        let mut v = vec!(index);
        let mut tok = token;
        while let Some(ix) = tok.next() {
            v.push(ix);
            tok = self.tokens[ix].clone();
        }
        v
    }
}

/// A lightweight reference into the parsed keytree string.
#[derive(Clone, Copy, Debug)]
pub struct KeyTreeRef<'a>(&'a KeyTree<'a>, pub usize);

impl<'a> KeyTreeRef<'a> {

    /// Useful for debugging.
    pub fn current_line(&self) -> usize {
        self.0.tokens[self.1].line()
    }

    pub (crate) fn top_token(&self) -> &'a Token<'a> {
        &self.0.tokens[self.1]
    }

    // Return child of the top token. If the top token is a Token::KeyValue then panic.
    pub (crate) fn top_child(&self, key: &str) -> Option<usize> {
        let top_token = self.top_token();

        match top_token {
            Token::KeyValue {..} => panic!(),
            Token::Key { children, .. } => {

                for (k, ix) in children {
                    if &key == k {
                        return Some(*ix)
                    }
                }
                return None
            },
        }
    }

    fn set_cursor(&mut self, ix: usize) {
        self.1 = ix;
    }

    pub (crate) fn assert_top_token_is_keyvalue(&self) -> Result<()> {
        match self.top_token() {
            Token::KeyValue {..} => Ok(()),
            Token::Key { key, line, .. } => {
                Err(err(
                    file!(), line!(),
                    &format!("Expected keyvalue found key {} at {}.",
                        key,
                        line,
                    )
                ))
            },
        }
    }

    pub (crate) fn assert_top_token_is_segment(&self, parent_segment: &str) -> Result<()> {
        if self.top_token().key() == parent_segment {
            Ok(())
        } else {
            Err(err(file!(), line!(),
                &format!("First segment mismatch {} {} at {}.",
                    &self.top_token(),
                    parent_segment,
                    self.top_token().line(),
                )
            ))
        }
    }

    pub (crate) fn key_into<T>(self) -> Result<T>
    where
        KeyTreeRef<'a>: TryInto<T>,
        KeyTreeRef<'a>: TryInto<T, Error = Error>,
    {
        // Use the client implementation `TryInto<T> for KeyTreeRef`.
        self.try_into()
    }

    pub (crate) fn keyvalue_into<T>(&self) -> Result<T>
    where
        T: FromStr,
    {
        self.assert_top_token_is_keyvalue()?;
        let token = self.top_token();

        T::from_str(token.value())
            .map_err(|_| err(file!(), line!(),
                &format!("Failed to parse {} at {}.",
                    token,
                    token.line(),
                )
            ))
    }

    /// Returns a `Some<KeyTree>` if the path exists or `None` otherwise.
    pub fn opt_at<T>(&self, key_path: &str) -> Result<Option<T>>
    where
        KeyTreeRef<'a>: TryInto<T>,
        KeyTreeRef<'a>: TryInto<T, Error = Error>,
    {
        let path = KeyPath::from_str(key_path);
        let kts = self.resolve_path(&path)?;
        match kts.len() {
            0 => Ok(None),
            1 => Ok(Some(kts[0].key_into()?)),
            _ => Err(err(
                file!(),
                line!(),
                &format!("Expected unique keyvalue found multi at {}.", key_path),
            )),
        }
    }

    /// Returns a `KeyTree`.
    pub fn at<T>(&self, key_path: &str) -> Result<T>
    where
        KeyTreeRef<'a>: TryInto<T>,
        KeyTreeRef<'a>: TryInto<T, Error = Error>,
    {
        let path = KeyPath::from_str(key_path);
        let kts = self.resolve_path(&path)?;
        match kts.len() {
            0 => Err(err(
                file!(),
                line!(),
                &format!("Expected unique keyvalue found none at {}.", key_path),
            )),
            1 => Ok(kts[0].key_into()?),
            _ => Err(err(
                file!(),
                line!(),
                &format!("Expected unique keyvalue found multi at {}.", key_path),
            )),
        }
    }

    /// ```
    /// use std::convert::TryInto;
    /// use std::str::FromStr;
    /// 
    /// use keytree::{KeyTree, KeyTreeRef};
    /// use keytree::Error;
    ///  
    /// static TEMP: &'static str = r#"
    /// example:
    ///     temp: -15.3
    /// "#;
    ///  
    /// #[derive(Debug)]
    /// struct Temperature(f32);
    /// 
    /// impl FromStr for Temperature {
    ///     type Err = std::num::ParseFloatError;
    /// 
    ///     fn from_str(s: &str) -> Result<Self, Self::Err> {
    ///         s.parse()
    ///     }
    /// }
    ///  
    /// impl<'a> TryInto<Temperature> for KeyTreeRef<'a> {
    ///     type Error = Error;
    ///  
    ///     fn try_into(self) -> Result<Temperature, Error> {
    ///         Ok(Temperature(self.value("example::temp")?))
    ///     }
    /// }
    ///  
    /// fn main() {
    ///     let kt = KeyTree::parse(TEMP).unwrap();
    ///     let temp: Temperature = kt.to_ref().try_into().unwrap();
    ///     println!("{:?}", temp);
    ///     // Temperature(-15.3)
    /// }
    /// ```
    pub fn value<T>(&self, key_path: &str) -> Result<T>
    where 
        T: FromStr,
    {
        let path = KeyPath::from_str(key_path);
        let kts = self.resolve_path(&path)?;
        match kts.len() {
            0 => Err(err(
                file!(),
                line!(),
                &format!("Expected unique keyvalue found none at {}.", key_path),
            )),
            1 => Ok(kts[0].keyvalue_into()?),
            _ => Err(err(
                file!(),
                line!(),
                &format!("Expected unique keyvalue found multi at {}.", key_path),
            )),
        }
    }

    /// Returns an `Option<T: FromStr>` where `Option<T>` is the receiver type. Returns `None` if
    /// the path does not exist.
    pub fn opt_value<T>(&self, key_path: &str) -> Result<Option<T>>
    where 
        T: FromStr,
    {
        let path = KeyPath::from_str(key_path);
        let kts = self.resolve_path(&path)?;
        match kts.len() {
            0 => Ok(None),
            1 => Ok(Some(kts[0].keyvalue_into()?)),
            _ => Err(err(
                file!(),
                line!(),
                &format!("Expected unique keyvalue found multi at {}.", key_path),
            )),
        }
    }

    /// Returns a `Vec<T: FromStr>` where `Vec<T>` is the receiver type. Expects at least one
    /// key-value. Use `opt_vec_value` if an empty `Vec` is permissible.
    pub fn vec_value<T>(&self, key_path: &str) -> Result<Vec<T>>
    where
        T: FromStr,
    {
        let path = KeyPath::from_str(key_path);
        let kts = self.resolve_path(&path)?;

        let mut v = Vec::new();
        for kt in kts {
            v.push(kt.keyvalue_into()?)
        }
        if v.is_empty() {
            return Err(
                err(file!(), line!(), &format!("Expected non-empty collection at {}.", key_path))
            )
        };
        Ok(v)
    }

    /// Returns a `Vec<T: FromStr>` where `Vec<T>` is the receiver type. The `Vec` can be empty.
    pub fn opt_vec_value<T>(&self, key_path: &str) -> Result<Vec<T>>
    where
        T: FromStr,
    {
        let path = KeyPath::from_str(key_path);
        let kts = self.resolve_path(&path)?;

        let mut v = Vec::new();
        for kt in kts {
            v.push(kt.keyvalue_into()?)
        }
        Ok(v)
    }

    /// Returns a `Vec<T>` where `T` can be coerced from a KeyTree. Fails if the path does not
    /// exist.
    pub fn vec_at<T>(&self, key_path: &str) -> Result<Vec<T>>
    where
        KeyTreeRef<'a>: TryInto<T>,
        KeyTreeRef<'a>: TryInto<T, Error = Error>,
    {
        let path = KeyPath::from_str(key_path);
        let kts = self.resolve_path(&path)?;
        
        let mut v = Vec::new();
        for kt in kts {
            v.push(kt.key_into()?)
        }
        if v.is_empty() {
            return Err(
                err(file!(), line!(), &format!("Expected non-empty collection at {}.", key_path))
            )
        };
        Ok(v)
    }

    /// Returns a `Vec<T>` where `T` can be coerced from a KeyTree. If the path does not exist
    /// returns an empty `Vec`.
    pub fn opt_vec_at<T>(&self, key_path: &str) -> Result<Vec<T>>
    where
        KeyTreeRef<'a>: TryInto<T>,
        KeyTreeRef<'a>: TryInto<T, Error = Error>,
    {
        let path = KeyPath::from_str(key_path);
        let kts = self.resolve_path(&path)?;
        
        let mut v = Vec::new();
        for kt in kts {
            v.push(kt.key_into()?)
        }
        Ok(v)
    }

    // Takes a `KeyPath` and follows it through the tree, returning a Vec of `KeyTreeRef`s.
    pub (crate) fn resolve_path(self, key_path: &KeyPath) -> Result<Vec<Self>> {

        // Keypaths are unique and keypaths cannot resolve on multiple siblings. We keep following
        // a path until we run out of segments. The we find the siblings of that unique path.

        match (self.top_token(), key_path.is_last()) {

            (Token::Key {..}, true) => {

                let parent_segment = key_path.parent_segment();
                let child_segment = key_path.child_segment();

                self.assert_top_token_is_segment(&parent_segment)?;

                // Get the child, and then get the siblings of that child

                match self.top_child(&child_segment) {
                    None =>  Ok(Vec::new()),
                    Some(ix) => {
                        let mut v = Vec::new();
                        let mut kt = self.clone();
                        for sibling_ix in self.0.siblings(ix) {
                            kt.set_cursor(sibling_ix);
                            v.push(kt);
                        }
                        Ok(v)
                    },
                }
            },

            (Token::Key {..}, false) => {

                let mut path = key_path.clone();
                let child_segment = path.child_segment();
                let parent_segment = path.parent_segment();
                
                self.assert_top_token_is_segment(&parent_segment)?;

                // Get the child, and then call resolve on that child. 
               
                match self.top_child(&child_segment) {
                    None => {
                        Ok(Vec::new())   // Option
                    },
                    Some(ix) => {
                        let mut kt = self.clone();
                        kt.set_cursor(ix);
                        path.advance();
                        kt.resolve_path(&path)
                    },
                }
            },

            (Token::KeyValue { .. }, true) => {

                let mut kt = self.clone();
                let mut v = Vec::new();
                for sibling_ix in self.0.siblings(self.1) {
                    kt.set_cursor(sibling_ix);
                    v.push(kt);
                }
                Ok(v)
            },

            (Token::KeyValue { key, value, line, .. }, false) => {

                return Err(err(file!(), line!(),
                    &format!("Line {} keypath {}. Keypath_extends_beyond_keyvalue {}: {}.",
                        *line,
                        &key_path,
                        key,
                        value,
                    )
                ))
            },
        }
    }
}
