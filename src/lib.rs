// Redo the Keytree data-structure by dropping the original string and building a Vector of tokens,
// where tokens contain pointers to other tokens, and with debug information. This removes any
// pointers into the original string, making the data-structure more compact, and making it much
// easier for client libraries to use because there are not lifetimes to manage.

// Use macros to automate most TryInto implementations.

mod parser;
pub mod serialize;

use crate::parser::Parser;
use std::{
    cmp::Ordering,
    error::Error,
    fmt::{self, Display},
    path::{Path, PathBuf},
    str::FromStr,
};
use thiserror::Error as ThisError;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

// === Error ======================================================================================

// ---BadIndentTempError---------------------------------------------------------------------------

// This is required because we don't have complete information to form a BadIndentError

#[derive(ThisError, Debug, PartialEq)]
#[error("BadIndentError({indent})")]
pub(crate) struct BadIndentTempError {
    indent: usize,
}

impl BadIndentTempError {
    pub(crate) fn into_bad_indent(&self, line_num: usize) -> BadIndentError {
        BadIndentError {
            indent: self.indent,
            line_num,
        }
    }
}

// ---BadindentError--------------------------------------------------------------------------------
// Keys must be indent by multiples of 4.

#[derive(ThisError, Debug, PartialEq)]
#[error("BadIndentError({indent}, {line_num})")]
pub(crate) struct BadIndentError {
    indent: usize,
    line_num: usize,
}

// ---ColonError---------------------------------------------------------------------------
// Colons must not appear before a key.

#[derive(ThisError, Debug, PartialEq)]
#[error("ColonError({token}, {line_num})")]
pub(crate) struct ColonError {
    token: String,
    line_num: usize,
}

// ---ExpectedKey-----------------------------------------------------------------------------------

#[derive(Debug, PartialEq, ThisError)]
#[error("ExpectedKey({token}, {line_num})")]
pub(crate) struct ExpectedKey {
    token: Token,
    line_num: usize,
}

// ---EmptyStringError------------------------------------------------------------------------------

#[derive(ThisError, Debug, PartialEq)]
#[error("EmptyStringError")]
pub(crate) struct EmptyStringError;

// ---FileNotFound----------------------------------------------------------------------------------

#[derive(Debug, PartialEq)]
pub(crate) struct FileNotFound {
    path: PathBuf,
}

impl fmt::Display for FileNotFound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FileNotFound({})", self.path.display())
    }
}
impl Error for FileNotFound {}

// ---FirstSegmentMismatchError---------------------------------------------------------------------

#[derive(Debug, PartialEq, ThisError)]
#[error("FirstSegmentMismatchError({top_token}, {parent_segment}, {line_num})")]
pub(crate) struct FirstSegmentMismatchError {
    top_token: Token,
    parent_segment: String,
    line_num: usize,
}

// ---IncompleteCommentOrKeyError-------------------------------------------------------------------

#[derive(ThisError, Debug, PartialEq)]
#[error("IncompleteCommentOrKeyError({token}, {line_num})")]
pub(crate) struct IncompleteCommentOrKeyError {
    token: String,
    line_num: usize,
}

// ---IncompleteLineError---------------------------------------------------------------------------

#[derive(ThisError, Debug, PartialEq)]
#[error("IncompleteLineError({line_num})")]
pub(crate) struct IncompleteLineError {
    token: String,
    line_num: usize,
}

// ---KeyPathTooLongError---------------------------------------------------------------------------

#[derive(ThisError, Debug, PartialEq)]
#[error("KeyPathTooLongError({line_num})")]
pub(crate) struct KeyPathTooLongError {
    key_path: KeyPath,
    token: Token,
    line_num: usize,
}

// ---KeySearchError--------------------------------------------------------------------------------

#[derive(ThisError, Debug, PartialEq)]
#[error("KeySearchError({expected}, {found}, {key_path})")]
pub(crate) struct KeySearchError {
    expected: String,
    found: String,
    key_path: KeyPath,
}

fn key_search_error(expected: &str, found: &str, key_path: KeyPath) -> KeySearchError {
    KeySearchError {
        expected: expected.to_string(),
        found: found.to_string(),
        key_path,
    }
}

// ---KeyValueToStringError------------------------------------------------------------------------

#[derive(ThisError, Debug, PartialEq)]
#[error("KeyValueToStringError({token}, {line_num})")]
pub(crate) struct KeyValueToStringError {
    token: Token,
    line_num: usize,
}

// ---NoColonAfterKeyError-------------------------------------------------------------------------

// A error that occurs while parsing a keytree string. A colon is required after a key.

#[derive(ThisError, Debug, PartialEq)]
#[error("NoColonAfterKey({token}, {line_num})")]
pub(crate) struct NoColonAfterKeyError {
    token: String,
    line_num: usize,
}

// ---NoSpaceAfterKeyError-------------------------------------------------------------------------

// A error that occurs while parsing a keytree string. A space is required after the ending colon
// in a key.

#[derive(ThisError, Debug, PartialEq)]
#[error("NoSpaceAfterKeyError({token}, {line_num})")]
pub(crate) struct NoSpaceAfterKeyError {
    token: String,
    line_num: usize,
}

// ---NoTokensError--------------------------------------------------------------------------------

// A error that occurs while parsing a keytree string.

#[derive(ThisError, Debug, PartialEq)]
#[error("NoTokensError")]
pub(crate) struct NoTokensError;

// --TopTokenNotKeyValueError----------------------------------------------------------------------

#[derive(ThisError, Debug, PartialEq)]
#[error("TopTokenNotKeyValueError({top_token})")]
pub(crate) struct TopTokenNotKeyValueError {
    top_token: Token,
}

// ---UTFError-------------------------------------------------------------------------------------

#[derive(ThisError, Debug, PartialEq)]
#[error("UTFError()")]
pub(crate) struct UTFError;

// === KeyPath ====================================================================================

// Something like "abc::def::ghi". A `KeyPath` is used to follow keys into a key-tree. Think of
// `KeyPath` as an iterator with a double window looking into a (parent segment, child segment).
#[derive(Clone, Eq, Hash, PartialEq)]
pub(crate) struct KeyPath {
    segments: Vec<String>,

    // Must be within the range 0 .. segments.len() - 2.
    // only after
    // [abc::def::ghi]
    //   ^    ^
    //   0    1
    counter: usize,
}

impl KeyPath {
    pub(crate) fn is_last(&self) -> bool {
        // This function is checked before the counter advances.
        self.counter == self.segments.len() - 2
    }

    // #[test]
    // pub test_is_last() {
    // }

    pub(crate) fn advance(&mut self) {
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
    pub(crate) fn parent_segment(&self) -> String {
        self.segments[self.counter].clone()
    }

    // [abc::def::ghi]
    //        ^
    //        1
    //   Child is "ghi"
    pub(crate) fn child_segment(&self) -> String {
        self.segments[self.counter + 1].clone()
    }

    // FromStr trait is not implemented because this never returns an error.
    pub(crate) fn from_str(s: &str) -> Self {
        let v = s
            .split(':')
            .filter(|s| !s.is_empty())
            .map(String::from)
            .collect::<Vec<String>>();
        KeyPath {
            segments: v,
            counter: 0,
        }
    }
}

impl fmt::Debug for KeyPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl Display for KeyPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, segment) in self.segments.iter().enumerate() {
            write!(f, "{}", segment)?;
            if i < self.segments.len() - 1 {
                write!(f, "::")?
            };
        }
        Ok(())
    }
}

impl Ord for KeyPath {
    fn cmp(&self, other: &Self) -> Ordering {
        for n in 0..self.segments.len() {
            match self.segments[n].cmp(&other.segments[n]) {
                Ordering::Less => return Ordering::Less,
                Ordering::Greater => return Ordering::Greater,
                Ordering::Equal => {}
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for KeyPath {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.segments.cmp(&other.segments))
    }
}

// === Keytree ====================================================================================

// Holds the token data.
#[derive(Debug)]
struct KeyTreeData(Vec<Token>);

impl KeyTreeData {
    // No bounds checking.
    pub(crate) fn token(&self, ix: usize) -> Token {
        self.0[ix].clone()
    }

    pub(crate) fn new() -> Self {
        KeyTreeData(Vec::new())
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn append_token(&mut self, tok: Token) -> usize {
        self.0.push(tok);
        self.0.len() - 1
    }

    // No bounds checking.
    pub(crate) fn siblings(&self, ix: usize) -> Vec<usize> {
        let mut acc = Vec::new();
        let mut token = self.token(ix);
        acc.push(ix);
        // Recursive
        while let Some(ix) = token.next() {
            acc.push(ix);
            token = self.token(ix);
        }
        acc
    }
}

// Clone just clones the part of the Vec that is on the stack.
impl Clone for KeyTreeData {
    fn clone(&self) -> Self {
        KeyTreeData(self.0.clone())
    }
}

// === DebugInfo ====================================================================================

// Pass around KeyTree level debugging info.
#[derive(Debug)]
pub(crate) struct DebugInfo {
    _last_path: Option<KeyPath>,
    file: Option<PathBuf>,
}

impl DebugInfo {
    pub(crate) fn new(file: Option<&Path>) -> DebugInfo {
        DebugInfo {
            _last_path: None,
            file: file.map(|p| p.to_path_buf()),
        }
    }
}

// We'll implement this explicitly because when the struct becomes more powerful, we'll want to
// result its history.
impl Clone for DebugInfo {
    fn clone(&self) -> Self {
        Self {
            _last_path: None,
            file: self.file.clone(),
        }
    }
}

// === Token ======================================================================================

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Token {
    Key {
        key: String,
        children: Vec<usize>,
        next: Option<usize>,
        debug: TokenDebugInfo,
    },
    KeyValue {
        key: String,
        value: String,
        next: Option<usize>,
        debug: TokenDebugInfo,
    },
}

impl Token {
    pub(crate) fn debug_info(&self) -> &TokenDebugInfo {
        match self {
            Token::Key { debug, .. } => debug,
            Token::KeyValue { debug, .. } => debug,
        }
    }

    pub(crate) fn key(&self) -> &String {
        match self {
            Token::Key { key, .. } => key,
            Token::KeyValue { key, .. } => key,
        }
    }

    // Will panic if called on a Token::Key. Always check before invoking this function.
    pub(crate) fn value(&self) -> &String {
        match self {
            Token::Key { .. } => panic!("This is a bug"),
            Token::KeyValue { value, .. } => value,
        }
    }

    pub(crate) fn next(&self) -> Option<usize> {
        match self {
            Token::Key { next: n, .. } => *n,
            Token::KeyValue { next: n, .. } => *n,
        }
    }

    #[allow(dead_code)]
    fn children(&self) -> Vec<usize> {
        match self {
            Token::Key { children, .. } => children.to_vec(),
            Token::KeyValue { .. } => panic!("This is a bug"),
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Key { key, .. } => write!(f, "{}:", key),
            Token::KeyValue { key, value, .. } => {
                write!(f, "{}: {}", key, value)
            }
        }
    }
}

// === TokenDebugInfo ==================================================================================

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct TokenDebugInfo {
    line_num: usize,
}

impl TokenDebugInfo {
    pub(crate) fn line_num(&self) -> usize {
        self.line_num
    }
}

// === KeyTree ========================================================================================

#[derive(Debug)]
pub struct KeyTree {
    data: KeyTreeData,
    index: usize,
}

impl KeyTree {
    /// Parse a string into a data-structure.
    /// ```
    /// use std::convert::TryInto;
    /// use std::error::Error;
    /// use key_tree::KeyTree;
    ///
    /// static HOBBITS: &'static str = r"
    /// hobbit:
    ///     name:         Frodo Baggins
    ///     age:          60
    ///     friends:
    ///         hobbit:
    ///             name: Bilbo Baggins
    ///             age:  111
    ///         hobbit:
    ///             name: Samwise Gamgee
    ///             age:  38
    ///             nick: Sam
    /// ";
    ///
    /// #[derive(Debug)]
    /// struct Hobbit {
    ///     name: String,
    ///     age: u32,
    ///     friends: Vec<Hobbit>,
    ///     nick: Option<String>,
    /// }
    ///
    /// impl TryInto<Hobbit> for KeyTree {
    ///     type Error = Box<dyn Error>;
    ///
    ///     fn try_into(self) -> Result<Hobbit, Self::Error> {
    ///         Ok(
    ///             Hobbit {
    ///                 name:       self.from_str("hobbit::name")?,
    ///                 age:        self.from_str("hobbit::age")?,
    ///                 friends:    self.opt_vec_at("hobbit::friends::hobbit")?,
    ///                 nick:       self.opt_from_str("hobbit::nick")?,
    ///             }
    ///         )
    ///     }
    /// }
    ///
    /// let hobbit: Hobbit = KeyTree::parse_str(HOBBITS)
    ///     .unwrap()
    ///     .try_into()
    ///     .unwrap();
    /// ```
    pub fn parse_str(s: &str) -> Result<KeyTree> {
        let (data, _) = Parser::parse_str(s)?;
        Ok(Self::new(data))
    }

    /// Parse a file into a data-structure.
    /// ```ignore
    /// let hobbit: Hobbit = KeyTree::parse("hobbits.keytree")
    ///     .unwrap()
    ///     .try_into()
    ///     .unwrap();
    /// ```
    pub fn parse<P: AsRef<Path>>(path: P) -> Result<KeyTree> {
        let (data, _) = Parser::parse(path)?;
        Ok(Self::new(data))
    }

    pub(crate) fn new(data: KeyTreeData) -> Self {
        KeyTree { data, index: 0 }
    }

    // TODO impl Clone

    pub(crate) fn top_token(&self) -> &Token {
        &self.data.0[self.index]
    }

    // Return child of the top token. If the top token is a Token::KeyValue then panic.
    pub(crate) fn top_child(&self, key: &str) -> Option<usize> {
        let top_token = self.top_token();

        match top_token {
            Token::KeyValue { .. } => panic!("This is a bug"),
            Token::Key { children, .. } => children
                .iter()
                .find(|&&ix| self.data.0[ix].key() == key)
                .copied(),
        }
    }

    fn set_cursor(&mut self, ix: usize) {
        self.index = ix;
    }

    pub(crate) fn assert_top_token_is_keyvalue(&self) -> Result<()> {
        match self.top_token() {
            Token::KeyValue { .. } => Ok(()),
            Token::Key { .. } => {
                return Err(Box::new(TopTokenNotKeyValueError {
                    top_token: self.top_token().clone(),
                }))
            }
        }
    }

    pub(crate) fn assert_top_token_is_segment(&self, parent_segment: &str) -> Result<()> {
        if self.top_token().key() == parent_segment {
            Ok(())
        } else {
            Err(Box::new(FirstSegmentMismatchError {
                top_token: self.top_token().clone(),
                parent_segment: parent_segment.into(),
                line_num: self.top_token().debug_info().line_num(),
            }))
        }
    }

    pub(crate) fn key_into<T>(self) -> Result<T>
    where
        KeyTree: TryInto<T>,
        KeyTree: TryInto<T, Error = Box<dyn Error>>,
    {
        // Use the client implementation `TryInto<T> for KeyTree`.
        self.try_into()
    }

    pub(crate) fn keyvalue_into<T>(&self) -> Result<T>
    where
        T: FromStr,
    {
        self.assert_top_token_is_keyvalue()?;
        let token = self.top_token();

        T::from_str(token.value()).map_err(|_| {
            Box::new(KeyValueToStringError {
                token: token.clone(),
                line_num: token.debug_info().line_num(),
            })
            .into()
        })
    }

    /// Parses a `KeyTree` token into an optional value.
    pub fn opt_at<T>(&self, kp: &str) -> Result<Option<T>>
    where
        KeyTree: TryInto<T>,
        KeyTree: TryInto<T, Error = Box<dyn Error>>,
    {
        let key_path = KeyPath::from_str(kp);
        let kts = self.resolve_path(&key_path)?;
        match kts.len() {
            0 => Ok(None),
            1 => Ok(Some(kts[0].clone().key_into()?)),
            _ => Err(Box::new(key_search_error("unique", "multi", key_path))),
        }
    }

    /// Parses a `KeyTree` token into a value.
    pub fn at<T>(&self, kp: &str) -> Result<T>
    where
        Self: TryInto<T, Error = Box<dyn Error>>,
    {
        let key_path = KeyPath::from_str(kp);
        let kts = self.resolve_path(&key_path)?;
        match kts.len() {
            0 => Err(Box::new(key_search_error(
                "unique keyvalue",
                "none",
                key_path,
            ))),
            1 => Ok(kts[0].clone().key_into()?),
            _ => Err(Box::new(key_search_error(
                "unique keyvalue",
                "multi",
                key_path,
            ))),
        }
    }

    // ```
    // use std::convert::TryInto;
    // use std::str::FromStr;
    //
    // use keytree::KeyTree;
    //
    // static TEMP: &'static str = r#"
    // example:
    //     temp: -15.3
    // "#;
    //
    // #[derive(Debug)]
    // struct Temperature(f32);
    //
    // impl FromStr for Temperature {
    //     type Err = std::num::ParseFloatError;
    //
    //     fn from_str(s: &str) -> Result<Self, Self::Err> {
    //         s.parse()
    //     }
    // }
    //
    // impl<'a> TryInto<Temperature> for KeyTree {
    //     type Error = Error;
    //
    //     fn try_into(self) -> Result<Temperature, Error> {
    //         Ok(Temperature(self.from_str("example::temp")?))
    //     }
    // }
    //
    // fn main() {
    //     let kt = KeyTree::parse(TEMP).unwrap();
    //     let temp: Temperature = kt.try_into().unwrap();
    //     println!("{:?}", temp);
    //     // Temperature(-15.3)
    // }
    // ```

    pub fn from_str<T>(&self, kp: &str) -> Result<T>
    where
        T: FromStr,
    {
        let key_path = KeyPath::from_str(kp);
        let kts = self.resolve_path(&key_path)?;
        match kts.len() {
            0 => Err(Box::new(key_search_error(
                "unique keyvalue",
                "none",
                key_path,
            ))),
            1 => Ok(kts[0].keyvalue_into()?),
            _ => Err(Box::new(key_search_error(
                "unique keyvalue",
                "multi",
                key_path,
            ))),
        }
    }

    /// Returns an `Option<T: FromStr>` where `Option<T>` is the receiver type. Returns `None` if
    /// the path does not exist.
    pub fn opt_from_str<T>(&self, kp: &str) -> Result<Option<T>>
    where
        T: FromStr,
    {
        let key_path = KeyPath::from_str(kp);
        let kts = self.resolve_path(&key_path)?;
        match kts.len() {
            0 => Ok(None),
            1 => Ok(Some(kts[0].keyvalue_into()?)),
            _ => Err(Box::new(KeySearchError {
                expected: "unique keyvalue".into(),
                found: "multi".into(),
                key_path,
            })),
        }
    }

    /// Returns a `Vec<T: FromStr>` where `Vec<T>` is the receiver type. Expects at least one
    /// key-value. Use `opt_vec_value` if an empty `Vec` is permissible.
    pub fn vec_from_str<T>(&self, kp: &str) -> Result<Vec<T>>
    where
        T: FromStr,
    {
        let key_path = KeyPath::from_str(kp);
        let kts = self.resolve_path(&key_path)?;

        let mut v = Vec::new();
        for kt in kts {
            v.push(kt.keyvalue_into()?)
        }
        if v.is_empty() {
            return Err(Box::new(KeySearchError {
                expected: "collection".into(),
                found: "empty".into(),
                key_path,
            }));
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
    pub fn vec_at<T>(&self, kp: &str) -> Result<Vec<T>>
    where
        KeyTree: TryInto<T>,
        KeyTree: TryInto<T, Error = Box<dyn Error>>,
    {
        let key_path = KeyPath::from_str(kp);
        let kts = self.resolve_path(&key_path)?;

        let mut v = Vec::new();
        for kt in kts {
            v.push(kt.key_into()?)
        }
        if v.is_empty() {
            return Err(Box::new(key_search_error("collection", "empty", key_path)));
        };
        Ok(v)
    }

    /// Returns a `Vec<T>` where `T` can be coerced from a KeyTree. If the path does not exist
    /// returns an empty `Vec`.
    pub fn opt_vec_at<T>(&self, key_path: &str) -> Result<Vec<T>>
    where
        Self: TryInto<T>,
        Self: TryInto<T, Error = Box<dyn Error>>,
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
    pub(crate) fn resolve_path(&self, key_path: &KeyPath) -> Result<Vec<Self>> {
        match (self.top_token(), key_path.is_last()) {
            // Last segment of key.
            (Token::Key { .. }, true) => {
                let parent_segment = key_path.parent_segment();
                let child_segment = key_path.child_segment();

                self.assert_top_token_is_segment(&parent_segment)?;

                // Get the child, and then get the siblings of that child

                match self.top_child(&child_segment) {
                    None => Ok(Vec::new()),
                    Some(ix) => {
                        let mut v = Vec::new();
                        for sibling_ix in self.data.siblings(ix) {
                            let mut kt = self.clone();
                            kt.set_cursor(sibling_ix);
                            v.push(kt);
                        }
                        Ok(v)
                    }
                }
            }

            // Before the last segment of key.
            (Token::Key { .. }, false) => {
                let mut path = key_path.clone();
                let child_segment = path.child_segment();
                let parent_segment = path.parent_segment();

                self.assert_top_token_is_segment(&parent_segment)?;

                // Get the child, and then call resolve on that child.

                match self.top_child(&child_segment) {
                    None => {
                        Ok(Vec::new()) // Option
                    }
                    Some(ix) => {
                        let mut kt = self.clone();
                        kt.set_cursor(ix);
                        path.advance();
                        kt.resolve_path(&path)
                    }
                }
            }

            // Last segment of keyvalue.
            (Token::KeyValue { .. }, true) => {
                let mut v = Vec::new();
                for sibling_ix in self.data.siblings(self.index) {
                    let mut kt = self.clone();
                    kt.set_cursor(sibling_ix);
                    v.push(kt);
                }
                Ok(v)
            }

            // Before the last segment of keyvalue. If such as unresolved keypath is a keyvalue
            // then return an error.
            (tok @ Token::KeyValue { debug, .. }, false) => {
                return Err(Box::new(KeyPathTooLongError {
                    key_path: key_path.clone(),
                    token: tok.clone(),
                    line_num: debug.line_num(),
                }))
            }
        } // match {
    }
}

impl Clone for KeyTree {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            index: self.index,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use indoc::indoc;

    fn debug() -> TokenDebugInfo {
        TokenDebugInfo { line_num: 42 }
    }

    fn key_token() -> Token {
        Token::Key {
            key: "key".to_owned(),
            children: vec![1],
            next: None,
            debug: debug(),
        }
    }

    fn keyval_token() -> Token {
        Token::KeyValue {
            key: "key".to_owned(),
            value: "value".to_owned(),
            next: None,
            debug: debug(),
        }
    }

    // === KeyPath ================================================================================

    #[test]
    fn display_should_work() {
        let s = "abc::def::ghi";
        assert_eq!(KeyPath::from_str(s).to_string(), s)
    }

    #[test]
    fn key_path_should_be_comparable() {
        assert!(KeyPath::from_str("aaa::aaa") < KeyPath::from_str("aaa::aab"))
    }

    // === DebugInfo ==============================================================================

    #[test]
    fn debuginfo_new_should_work() {
        DebugInfo::new(Some(&Path::new("test")));
    }

    // === Token tests ============================================================================

    #[test]
    fn key_token_should_work() {
        let _tok = key_token();
    }

    #[test]
    fn keyval_token_should_work() {
        let _tok = keyval_token();
    }

    #[test]
    fn token_should_have_debug_info() {
        let tok = keyval_token();
        assert_eq!(tok.debug_info().line_num, 42);
    }

    #[test]
    fn token_should_have_key() {
        let tok = keyval_token();
        assert_eq!(tok.key(), &"key".to_owned());
    }

    #[test]
    fn keyval_token_should_have_value() {
        let tok = keyval_token();
        assert_eq!(tok.value(), &"value".to_owned());
    }

    // === KeyTreeData tests ===================================================================

    #[test]
    fn next_sibling_should_be_set() {
        let s = indoc!(
            "
            key1:
                keyval: a
                keyval: b"
        );
        let kt = Parser::parse_str(&s).unwrap().0;
        assert_eq!(kt.0[1].next(), Some(2));
    }

    #[test]
    fn should_get_siblings() {
        let s = indoc!(
            "
            key1:
                keyval: a
                keyval: b"
        );
        let kt = KeyTree::parse_str(&s).unwrap();
        assert!(kt.data.siblings(1) == vec![1, 2]);
    }

    // === KeyTree search tests ===================================================================

    #[test]
    fn should_parse() {
        let s = indoc! {r"
            hobbit:
                name: Frodo Baggins
                age:  60
            "};
        let kt = KeyTree::parse_str(&s).unwrap();

        assert_eq!(kt.data.0[0].children(), vec![1, 2]);
        assert_eq!(kt.data.0[1].value(), "Frodo Baggins");
        assert_eq!(kt.data.0[2].value(), "60");
    }

    #[test]
    fn should_parse_and_coerce() {
        #[derive(Debug)]
        #[allow(dead_code)]
        struct Hobbit {
            name: String,
            age: u32,
        }

        impl TryInto<Hobbit> for KeyTree {
            type Error = Box<dyn Error>;

            fn try_into(self) -> Result<Hobbit> {
                Ok(Hobbit {
                    name: self.from_str("hobbit::name")?,
                    age: self.from_str("hobbit::age")?,
                })
            }
        }

        let s = indoc! {r"
            hobbit:
                name: Frodo Baggins
                age:  60
            "};
        let kt = KeyTree::parse_str(&s).unwrap();

        assert_eq!(kt.data.0[2].value(), "60");

        let kt: KeyTree = KeyTree::parse_str(&s).unwrap();
        let _: Hobbit = kt.try_into().unwrap();
    }

    // === KeyTree ================================================================================

    #[test]
    fn parse_should_fail_if_file_missing() {
        match KeyTree::parse("missing") {
            Ok(_) => assert!(false),
            Err(e) => {
                assert_eq!(e.to_string(), "FileNotFound(missing)",)
            }
        }
    }

    // === TryInto derive =========================================================================

    // #[test]
    // fn should_derive() {

    //     use std::str::FromStr;
    //     use keytree_derive::KeyTree;

    //     #[derive(Debug, KeyTree)]
    //     struct Hobbit {
    //          name: String,
    //          age:  u32,
    //     }

    //     let s = indoc! {r"
    //         hobbit:
    //             name: Frodo Baggins
    //             age:  60
    //         "};
    //     let kt = KeyTree::parse_str(&s).unwrap();

    //     assert_eq!(kt.data.0[2].value(), "60");

    //     let kt: KeyTree = KeyTree::parse_str(&s).unwrap();
    //     let hobbit: Hobbit = kt.try_into().unwrap();
    // }
}
