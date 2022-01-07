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
//!
//! Then we need to implement `TryInto<Hobbit>` to deserialize the string into a Rust
//! data-structure,
//!
//! ```
//! impl<'a> TryInto<Hobbit> for KeyTreeRef<'a> {
//!     type Error = Error;
//! 
//!     fn try_into(self) -> Result<Hobbit, Error> {
//!         Ok(
//!             Hobbit {
//!
//!                 // use the `from_str` implementation of `String` to get a `name`.
//!                 name: self.from_str("hobbit::name")?,
//!
//!                 // use the `from_str` implementation `u32` to get an `age`.
//!                 age: self.from_str("hobbit::age")?,
//!
//!                 // use the `TryInto<Hobbit> implementation to get a `Vec<Hobbit>`.
//!                 friends: self.opt_vec_at("hobbit::friends::hobbit")?,
//!
//!                 // uses the `from_str` implementation for `String` to get an `Option<String>`.
//!                 // If the keypath does not exist it returns `None`.
//!                 nick: self.opt_from_str("hobbit::nick")?,
//!             }
//!         )
//!     }
//! }
//! ```
//!
//! Functions that make a selection from the keytree string and deserialize it are
//! ```
//! self.at("abc::def::ghi")?
//! ```
//! ```
//! self.opt_at("abc::def::ghi")?
//! ```
//! ```
//! self.vec_at("abc::def::ghi")?
//! ```
//! ```
//! self.opt_vec_at("abc::def::ghi")?
//! ```
//! ```
//! self.from_str("abc::def::ghi")?
//! ```
//! ```
//! self.opt_from_str("abc::def::ghi")?
//! ```
//! ```
//! self.opt_vec_from_str("abc::def::ghi")?
//! ```
//!
//! The deserializing function should look something like
//!
//! ``` 
//!     // Creates an 'abstract syntax tree' which is just a set of references into the keytree string s.
//!     let kt = KeyTree::parse(s).unwrap();
//!
//!     // kt.to_ref() creates a reference to kt.
//!     // try_into() does all the deserialization work.
//!     let hobbit: Hobbit = kt.to_ref().try_into().unwrap();
//!     &dbg!(&hobbit);
//!
//! ```
//! ## KeyTree Syntax Specification 
//! 
//! - Indentation has meaning and is 4 spaces, relative to the top key. Since indenting is relative
//! to the top key, then you can neatly align strings embedded in code.
//! 
//! - Each line can be empty, have whitespace only, be a comment, be a key, or be a key/value pair.
//! 
//! - There are keys and values. Key/value pairs look like
//! 
//! ```text
//! name: Frodo
//! ```
//! Keys have children indented 4 spaces below them. The children can be either keys or key/value pairs.
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
//! is a collection of hobbits. Sibling keys with the same name must be contiguous. 
//! 
//! - Keys must not include but must be followed by a colon `:`.
//! 
//! - Values are all characters between the combination of ':' and whitespace and the end of the
//! line. The value is trimmed of whitespace at both ends.
//! 
//! - Comments can only be on their own line. A comment line starts with any amount of whitespace followed by `//`.
//! 
//! ```text
//! // comment
//! hobbit:
//!     // another comment
//!     name: Frodo
//! ```

#![forbid(unsafe_code)]

mod builder;

#[macro_use]
pub mod error;

pub(crate) mod parser;
pub mod serialize;

use std::convert::TryInto;
use std::fmt;
use std::fmt::Display;
use std::str::FromStr;

use crate::error::*;

use crate::parser::Builder;

type Result<T> = std::result::Result<T, Error>;
type DynResult<T> = std::result::Result<T, Box<dyn std::error::Error>>;

// Somethin like "abc::def::ghi". A `KeyPath` is used to follow keys into a keytree. Think of
// `KeyPath` as an iterator with a double window looking into a (parent segment, child segment).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub (crate) struct KeyPath {
    segments: Vec<String>,
    
    // Must be within the range 0 .. segments.len() - 2.
    // only after
    // [abc::def::ghi]
    //   ^    ^
    //   0    1
    counter: usize,
}

impl KeyPath {

    pub (crate) fn is_last(&self) -> bool {
        // This function is checked before the counter advances.
        self.counter == self.segments.len() - 2
    }

    // #[test]
    // pub test_is_last() {
    // }

    pub (crate) fn advance(&mut self) {
        self.counter += 1;
        if self.counter >= self.segments.len() {
            println!("Keypath has exceeded end.");
            panic!()
        };
    }

    // [abc::def::ghi]
    //        ^
    //        1
    //   Parent is "def"
    pub (crate) fn parent_segment(&self) -> String {
        self.segments[self.counter].clone()
    }

    // [abc::def::ghi]
    //        ^
    //        1
    //   Child is "ghi"
    pub (crate) fn child_segment(&self) -> String {
        self.segments[self.counter + 1].clone()
    }

    // FromStr trait is not implemented because this never returns an error.
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

trait StringConcat {
    fn string_concat<'a>(&self, f: fn (String) -> String) -> String;
}

impl StringConcat for Vec<String> {
    fn string_concat<'a>(&self, f: fn (String) -> String) -> String {
        let mut s = String::new();
        for segment in self {
            s.push_str(&f(segment.to_string()));
        }
        s
    }
}

impl Display for KeyPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = self.segments.string_concat(|seg| format!("{}::", seg));
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
pub struct KeyTree<'a>(Vec<Token<'a>>);

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
        let token = self.0[index].clone();
        
        let mut v = vec!(index);
        let mut tok = token;
        while let Some(ix) = tok.next() {
            v.push(ix);
            tok = self.0[ix].clone();
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
        self.0.0[self.1].line()
    }

    pub (crate) fn top_token(&self) -> &'a Token<'a> {
        &self.0.0[self.1]
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
                Err(err!(&format!("Expected keyvalue found key {} at {}.", key, line)))
            },
        }
    }

    pub (crate) fn assert_top_token_is_segment(&self, parent_segment: &str) -> Result<()> {
        if self.top_token().key() == parent_segment {
            Ok(())
        } else {
            Err(err!(
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
            .map_err(|_| err!( &format!("Failed to parse {} at {}.", token, token.line())))
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
            _ => Err(err!(&format!("Expected unique keyvalue found multi at {}.", key_path))),
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
            0 => Err(err!(&format!("Expected unique keyvalue found none at {}.", key_path))),
            1 => Ok(kts[0].key_into()?),
            _ => Err(err!(&format!("Expected unique keyvalue found multi at {}.", key_path))),
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
    ///         Ok(Temperature(self.from_str("example::temp")?))
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
    pub fn from_str<T>(&self, key_path: &str) -> Result<T>
    where 
        T: FromStr,
    {
        let path = KeyPath::from_str(key_path);
        let kts = self.resolve_path(&path)?;
        match kts.len() {
            0 => Err(err!(&format!("Expected unique keyvalue found none at {}.", key_path))),
            1 => Ok(kts[0].keyvalue_into()?),
            _ => Err(err!(&format!("Expected unique keyvalue found multi at {}.", key_path))),
        }
    }

    /// Returns an `Option<T: FromStr>` where `Option<T>` is the receiver type. Returns `None` if
    /// the path does not exist.
    pub fn opt_from_str<T>(&self, key_path: &str) -> Result<Option<T>>
    where 
        T: FromStr,
    {
        let path = KeyPath::from_str(key_path);
        let kts = self.resolve_path(&path)?;
        match kts.len() {
            0 => Ok(None),
            1 => Ok(Some(kts[0].keyvalue_into()?)),
            _ => Err(err!(&format!("Expected unique keyvalue found multi at {}.", key_path))),
        }
    }

    /// Returns a `Vec<T: FromStr>` where `Vec<T>` is the receiver type. Expects at least one
    /// key-value. Use `opt_vec_value` if an empty `Vec` is permissible.
    pub fn vec_from_str<T>(&self, key_path: &str) -> Result<Vec<T>>
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
            return Err(err!(&format!("Expected non-empty collection at {}.", key_path)))
        };
        Ok(v)
    }

    /// Returns a `Vec<T: FromStr>` where `Vec<T>` is the receiver type. The `Vec` can be empty.
    pub fn opt_vec_from_str<T>(&self, key_path: &str) -> Result<Vec<T>>
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
                err!(&format!("Expected non-empty collection at {}.", key_path))
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

        match (self.top_token(), key_path.is_last()) {

            // Last segment of key.
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

            // Before the last segment of key.
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

            // Last segment of keyvalue.
            (Token::KeyValue { .. }, true) => {

                let mut kt = self.clone();
                let mut v = Vec::new();
                for sibling_ix in self.0.siblings(self.1) {
                    kt.set_cursor(sibling_ix);
                    v.push(kt);
                }
                Ok(v)
            },

            // Before the last segment of keyvalue. If such as unresolved keypath is a keyvalue
            // then return an error.
            (Token::KeyValue { key, value, line, .. }, false) => {

                return Err(err!(
                    &format!("Line {} keypath {}. Keypath_extends_beyond_keyvalue {}: {}.",
                        *line,
                        &key_path,
                        key,
                        value,
                    )
                ))
            },

        } // match {
    }
}
