//! Module to serialize a Rust data-structure into a nicely-formatted keytree string.

use std::fmt;
use std::fmt::Display;

pub trait IntoKeyTree {
    fn keytree(&self) -> KeyTreeString;
}

pub enum Token {
    KeyToken(KeyToken),
    KeyValToken(KeyValToken),
    Comment(Comment),
}

impl Token {
    pub fn to_str(&self, val_indent: usize) -> String {
        match self {
            Token::KeyToken(kt) => kt.to_str(),
            Token::KeyValToken(kvt) => kvt.to_str(val_indent),
            Token::Comment(c) => c.to_str(),
        }
    }
}

pub struct KeyToken {
    indent: usize,
    key: String,
}

impl KeyToken {
    pub fn to_str(&self) -> String {
        let mut s = String::new();
        s.push_str(&padding(self.indent * 4));
        s.push_str(&self.key);
        s.push(':');
        s
    }
}

pub struct KeyValToken {
    indent: usize,
    key: String,
    val: String,
}

impl KeyValToken {
    pub fn to_str(&self, val_indent: usize) -> String {
        let mut s = String::new();
        s.push_str(&padding(self.indent * 4));
        s.push_str(&self.key);
        s.push_str(": ");
        s.push_str(&padding(val_indent - (self.key.len() + 2 + self.indent * 4)));
        s.push_str(&self.val);
        s
    }
}

pub struct Comment {
    indent: usize,
    comment: String,
}

impl Comment {
    pub fn to_str(&self) -> String {
        let mut s = String::new();
        s.push_str(&padding(self.indent * 4));
        s.push_str("// ");
        s.push_str(&self.comment);
        s
    }
}

pub struct KeyTreeString {
    tokens: Vec<Token>,

    /// The indentation in chars to align values.
    val_indent: usize,
}

impl KeyTreeString {
    pub fn new() -> Self {
        KeyTreeString {
            tokens: Vec::new(),
            val_indent: 0,
        }
    }

    /// Push a key token onto the String. The indent value is relative to the root indent.
    pub fn push_key(&mut self, indent: usize, key: &str) {
        let key = Token::KeyToken(
            KeyToken {
                indent: indent,
                key: String::from(key),
            }
        );
        self.tokens.push(key)
    }

    pub fn push_opt_value<T: Display>(&mut self, indent: usize, key: &str, value: Option<T>) {
        match value {
            None => return,
            Some(v) => {
                self.push_keyvalue(indent, key, v.to_string().as_str())
            },
        }
    }

    /// Push a key-value token onto the String. The indent value is relative to the root indent.
    pub fn push_keyvalue<T: Display>(&mut self, indent: usize, key: &str, value: T) {
        let kv = Token::KeyValToken(
            KeyValToken {
                indent: indent,
                key: String::from(key),
                val: value.to_string(),
            }
        );
        self.tokens.push(kv);

        //      |
        //      v
        // 012345 
        // key:  
        let key_len = key.chars().count() + (indent * 4) + 2;

        // |   |
        // v   v
        // 0123456
        let val_indent = match key_len % 4 {
            0 => key_len,
            1 => key_len + 3,
            2 => key_len + 2,
            3 => key_len + 1,
            _ => unreachable!(),
        };
                
        //  val_indent (5)
        //      |
        //      v
        // 012345
        // key:  
        //
        // (padding = val_indent - (key.len() + 2)

        if val_indent > self.val_indent {
            self.val_indent = val_indent;
        };
    }

    /// Push a comment onto the String. The indent value is relative to the root indent.
    pub fn push_comment(&mut self, indent: usize, comment: &str) {
        let comment = Token::Comment(
            Comment {
                indent: indent * 4,
                comment: String::from(comment),
            }
        );
        self.tokens.push(comment)
    } 

    /// Push a KeyTreeString on to the String. The indent value is relative to the root indent.
    pub fn push_keytree(&mut self, indent: usize, keytree: KeyTreeString) {
        for token in keytree.tokens {
            match token {
                Token::KeyToken(k) => {
                    self.push_key(k.indent + indent, &k.key);
                },
                Token::KeyValToken(kv) => {
                    self.push_keyvalue(kv.indent + indent, &kv.key, &kv.val);
                },
                Token::Comment(c) => {
                    self.push_comment(c.indent + indent, &c.comment);
                }
            }
        }
    }
}

impl fmt::Display for KeyTreeString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        for token in &self.tokens {
            match token {
                Token::KeyValToken(kvt) => s.push_str(&kvt.to_str(self.val_indent)),
                Token::KeyToken(kt) => s.push_str(&kt.to_str()),
                Token::Comment(com) => s.push_str(&com.to_str()),
            }
            s.push('\n');
        }
        write!(f, "{}", s)
    }
}

fn padding(len: usize) -> String {
    let mut s = String::new();
    for _ in 0..len {
        s.push(' ');
    }
    s
}

#[test]
fn test_1() {
    let mut kt_string = KeyTreeString::new();
    kt_string.push_keyvalue(1, "key", "value");
    assert_eq!(
        kt_string.to_string(),
        "    key:    value",
    )
}

#[test]
fn test_2() {
    let mut kt_string = KeyTreeString::new();
    kt_string.push_keyvalue(0, "key", "value");
    assert_eq!(
        kt_string.to_string(),
        "key:    value",
    )
}

#[test]
fn test_3() {
    let mut kt_string = KeyTreeString::new();
    kt_string.push_keyvalue(0, "ky", "value");
    assert_eq!(
        kt_string.to_string(),
        "ky: value",
    )
}

