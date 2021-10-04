//! A path such as `hobbit::friend`, used to select a key in
//! the tree.

use std::fmt;
use std::cmp::Ordering;
use std::fmt::Display;

/// A KeyPath it used to follow keys into a keytree.
#[derive(Clone, Eq, Hash, PartialEq)]
pub(crate) struct KeyPath(pub Vec<String>);

impl KeyPath {

    // pub (crate) fn new() -> Self {
    //     KeyPath(Vec::new())
    // }

    // pub (crate) fn truncate(&mut self, len: usize) {
    //     self.0.truncate(len);
    // }
    
    // pub (crate) fn append(&mut self, other: &mut KeyPath) {
    //     self.0.append(&mut other.0);
    // }

    // pub (crate) fn len(&self) -> usize {
    //     self.0.len()
    // }

    pub(crate) fn from_str(s: &str) -> Self {
        let v = s.split(':')
            .filter(|s| !s.is_empty())
            .map(|s| String::from(s))
            .collect::<Vec<String>>();
        KeyPath(v)
    }
}

impl fmt::Debug for KeyPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl Display for KeyPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, segment) in self.0.iter().enumerate() {
            write!(f, "{}", segment)?;
            if i < self.0.len() - 1 { write!(f, "::")? };
        };
        Ok(())
    }
}

impl Ord for KeyPath {
    fn cmp(&self, other: &Self) -> Ordering {
        for n in 0..self.0.len() {
            match self.0[n].cmp(&other.0[n]) {
                Ordering::Less => return Ordering::Less,
                Ordering::Greater => return Ordering::Greater,
                Ordering::Equal => {},
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for KeyPath {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

