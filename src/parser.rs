#![allow(dead_code)]

use crate::{DebugInfo, KeyTreeData, KeyTreeError, Result, Token, TokenDebugInfo};
use std::{fs, path::{Path, PathBuf}};
use std::{cmp::Ordering};

pub(crate) const INDENT_STEP: usize = 4;

// Parser state. Used in parser() function.
#[derive(Clone, Debug, PartialEq)]
enum PS {
    Fc,       // First char.
    Bk,       // Before key.
    Cok,      // Comment or key
    Ik,       // In key.
    Rak,      // The character right after the key.
    Ak,       // After key.
    Iv,       // In value.
    Cm,       // In comment
}

// Chars received
enum Punct  {
    Char, 
    Colon,
    ForwardSlash,
    Whitespace,
}

impl Punct {
    fn from_char(c: char) -> Self {
        if c.is_whitespace() { return Punct::Whitespace };
        match c {
            ':' => Punct::Colon,
            '/' => Punct::ForwardSlash,
            _ => Punct::Char
        }
    }
}

// === Builder ====================================================================================

// Holds on to some extra start while we are building a KeyTree.
#[derive(Debug)]
pub (crate) struct Builder {
    pub(crate) data: KeyTreeData,
    last_tokens: LastTokens,
    indent: usize, 
}

impl Builder {
    pub(crate) fn new() -> Builder {
        Builder {
            data: KeyTreeData::new(),
            last_tokens: LastTokens::new(),
            indent: 0,
        }
    }

    pub(crate) fn owned_keytree(self) -> KeyTreeData {
        self.data
    }

    pub(crate) fn append(&mut self, indent: usize, token: Token) -> Result<usize> {
        if self.data.is_empty() {
            self.append_first_token(indent, token)
        } else {
            self.append_non_first_token(indent, token)
        }
    }

    // Should only be called by append();
    pub(crate) fn append_first_token(&mut self, indent: usize, token: Token) -> Result<usize> {
        match token {
            token @ Token::KeyValue {..} => {
                return Err(KeyTreeError::Parse(
                    "Expected key found".to_string(),
                    token.to_string(),
                    1,
                ))
            },
            token @ Token::Key {..} => {
                let ix = 0;
                self.data.append_token(token);
                self.last_tokens.add(indent, ix);
            },
        }
        self.indent = indent;
        Ok(0)
    }

    fn set_parent_link(&mut self, indent: usize, child_ix: usize) {
        let parent_ix = self.last_tokens.parent(indent);
        self.set_link_to_child(parent_ix, child_ix);
    }

    fn set_next_link(&mut self, previous_sib_ix: usize, sib_ix: usize) {
        match self.data.0.get_mut(previous_sib_ix) {
            Some(Token::Key {next,..}) => *next = Some(sib_ix),
            Some(Token::KeyValue {ref mut next,..}) => *next = Some(sib_ix),
            None => { panic!("This is a bug") },
        }
    }

    fn set_link_to_child(&mut self, parent_ix: usize, child_ix: usize) {
        match &mut self.data.0.get_mut(parent_ix) {
            Some(Token::Key {children,..}) => {
                children.push(child_ix);
            },
            Some(Token::KeyValue {..}) => { panic!("This is a bug") },
            None => { panic!("This is a bug") },
        }
    }

    fn previous_sib_ix(&self, indent: usize, token: &Token) -> Option<usize> {
        match self.last_tokens.last(indent) {
            Some(previous_sib_ix) => {

                let previous_sib = self.data.token(previous_sib_ix);
                if previous_sib.key() == token.key() {
                    Some(previous_sib_ix)
                } else {
                    None
                }
            },
            None => None
        }
    }

    // This is the main function that builds a KeyTreeData. Should only be called by append();
    fn append_non_first_token(&mut self, new_indent: usize, token: Token) -> Result<usize> {

        let indent_delta = usize::cmp(&new_indent, &self.indent);

        let previous_sib_ix = self.previous_sib_ix(new_indent, &token);

        let ix = match (indent_delta, previous_sib_ix) {

            (Ordering::Greater, _) => {

                // Append the new token to the keytree Vec.
                let ix = self.data.append_token(token);

                // Set parent for every new token, other than those that have a previous sibling.
                self.set_parent_link(new_indent, ix);

                // Append the new token to last.
                self.last_tokens.add(new_indent, ix);

                ix
            },

            (Ordering::Equal, None) => {

                // Append the new token to the keytree Vec.
                let ix = self.data.append_token(token);

                // Set parent for every new token, other than those that have a previous sibling.
                self.set_parent_link(new_indent, ix);

                // Replace last
                self.last_tokens.replace_last_token(new_indent, ix);

                ix
            },
               
            // Sibling
            (Ordering::Equal, Some(previous_sib_ix)) => {

                // Append the new token to the keytree Vec.
                let ix = self.data.append_token(token);

                // Set sibling link.
                self.set_next_link(previous_sib_ix, ix);

                // Replace last
                self.last_tokens.replace_last_token(new_indent, ix);

                ix
            },

            (Ordering::Less, None) => {

                // Append the new token to the keytree Vec.
                let ix = self.data.append_token(token);

                // Set parent for every new token, other than those that have a previous sibling.
                self.set_parent_link(new_indent, ix);

                // Remove deeper last_tokens.
                self.last_tokens.remove_deeper_than(new_indent);

                // Replace last
                self.last_tokens.replace_last_token(new_indent, ix);

                ix
            },

            (Ordering::Less, Some(previous_sib_ix)) => {

                dbg!();

                // Append the new token to the keytree Vec.
                let ix = self.data.append_token(token);

                // Don't set parent link.
                
                // Remove deeper last_tokens.
                self.last_tokens.remove_deeper_than(new_indent);

                // Set sibling link.
                self.set_next_link(previous_sib_ix, ix);

                // Replace last
                self.last_tokens.replace_last_token(new_indent, ix);

                ix
            }
        };
        self.indent = new_indent;
        Ok(ix)
    }
}

// === LastTokens =================================================================================

// Keeps track of the last token at each indent level from 0 to current indent level. These parents
// can be thought of as 'in scope'.
#[derive(Debug)]
pub(crate) struct LastTokens(pub Vec<usize>);

impl LastTokens{
    pub(crate) fn new() -> Self {
        LastTokens(Vec::new())
    }

    // Returns the last token at a given indent level. Returns None if there is no parent at that
    // level. 
    pub(crate) fn last(&self, indent: usize) -> Option<usize> {
        if indent >= self.0.len() { return None }
        Some(self.0[indent])
    }
    
    // Remove parents deeper than indent, for example if indent is 2 then retain indents parents
    // with indents 0 and 1 and 2.
    pub(crate) fn remove_deeper_than(&mut self, indent: usize) {
        self.0.truncate(indent + 1)
    }

    // Replace last token. Will panic if there is an indent mismatch.
    pub(crate) fn replace_last_token(&mut self, indent: usize, ix: usize) {
        assert!(indent + 1 == self.0.len());
        self.0[indent] = ix;

    }

    // Add another token to list. Will panic if there is an indent mismatch.
    pub(crate) fn add(&mut self, indent: usize, ix: usize) {
        assert!(indent == self.0.len());
        self.0.push(ix);
    }

    // Return the parent index based on indent level.
    pub(crate) fn parent(&self, indent: usize) -> usize {
        if indent == 0 { panic!("This is a bug") };
        if indent > self.0.len() { panic!("this is a bug") };

        self.0[indent - 1]
    }
}


pub(crate) struct Parser;

impl Parser {

    pub fn parse_str(s: &str) -> Result<(KeyTreeData, DebugInfo)> {
        let path: Option<&Path> = None;
        Self::parse_inner(s, path)
    }

    pub fn parse<P: AsRef<Path>>(path: P) -> Result<(KeyTreeData, DebugInfo)> {
        let path: PathBuf = path.as_ref().to_path_buf();

        let path_string = path.to_str()
            .ok_or(KeyTreeError::IO(String::new()))?.to_string();

        let s = fs::read_to_string(&path).map_err(|_| KeyTreeError::IO(path_string))?;

        Self::parse_inner(&s, Some(&path))
    }

    // Parse a string into a `KeyTree`. If there is a filename, this can be input for error
    // handling. 
    pub fn parse_inner(s: &str, path_opt: Option<&Path>) -> Result<(KeyTreeData, DebugInfo)> {
        let debug_info = DebugInfo::new(path_opt);

        if s.is_empty() { return Err(KeyTreeError::ParseEmpty) };
        let lines = s.lines();

        // These variables are used by the parser to build tokens.
        let mut parse_state: PS;

        // Because of comments, lines do not correlate with items in the KeyTree Vec.  
        let mut line_num;

        let mut start_key;
        let mut end_key;
        let mut start_val;
        let mut root_indent     = None;

        // Keeps track of last pos when parsing line.
        let mut last_pos;

        // Tokens are passed to the Builder
        let mut builder = Builder::new();

        for (i, line) in lines.enumerate() {
            line_num = i + 1;

            parse_state = PS::Fc;
            start_key = 0;
            end_key = 0;
            start_val = 0;
            last_pos = 0;

            for (pos, ch) in line.char_indices() {

                last_pos = pos;

                match (&parse_state, Punct::from_char(ch)) {

                    // Matches are ordered by estimated rate of occurence.

                    // Whitespace, no errors.

                    (PS::Fc, Punct::Whitespace) => {
                        parse_state = PS::Bk;
                    },
                    (PS::Bk, Punct::Whitespace) => { },
                    (PS::Cm, Punct::Whitespace) => { },
                    (PS::Rak, Punct::Whitespace) => {
                        parse_state = PS::Ak;
                    },
                    (PS::Ak, Punct::Whitespace) => { },
                    (PS::Iv, Punct::Whitespace) => { },

                    // Char, no errors.

                    (PS::Ak, Punct::Char) => {
                        start_val = pos;
                        parse_state = PS::Iv;
                    },
                    (PS::Iv, Punct::Char) => {},
                    (PS::Fc, Punct::Char) => {
                        start_key = pos;
                        parse_state = PS::Ik;
                    },
                    (PS::Bk, Punct::Char) => {
                        start_key = pos;
                        parse_state = PS::Ik;
                    },
                    (PS::Cok, Punct::Char) => {
                        parse_state = PS::Ik;
                    },
                    (PS::Cm, Punct::Char) => { },
                    (PS::Ik, Punct::Char) => {}

                    // Colon, no errors

                    (PS::Cok, Punct::Colon) => {
                        parse_state = PS::Ik;
                    },
                    (PS::Cm, Punct::Colon) => { },
                    (PS::Iv, Punct::Colon) => {},
                    (PS::Ak, Punct::Colon) => {
                        start_val = pos;
                        parse_state = PS::Iv;
                    },
                    (PS::Ik, Punct::Colon) => {
                        end_key = pos - 1;
                        parse_state = PS::Rak;
                    }

                    // Forward slash, no errors

                    (PS::Cok, Punct::ForwardSlash) => {
                        parse_state = PS::Cm;
                    },
                    (PS::Fc, Punct::ForwardSlash) => {
                        start_key = pos;
                        parse_state = PS::Cok;
                    },
                    (PS::Cm, Punct::ForwardSlash) => {},
                    (PS::Bk, Punct::ForwardSlash) => {
                        start_key = pos;
                        parse_state = PS::Cok;
                    },
                    (PS::Ik, Punct::ForwardSlash) => {}
                    (PS::Ak, Punct::ForwardSlash) => {
                        start_val = pos;
                        parse_state = PS::Iv;
                    },
                    (PS::Iv, Punct::ForwardSlash) => {},

                    // Whitespace errors

                    (PS::Ik, Punct::Whitespace) => {
                        let token_str = &s[start_key..=pos - 1];
                        return parse_err("No colon after key", token_str, line_num)
                    },
                    (PS::Cok, Punct::Whitespace) => {
                        let token_str = &s[start_key..=pos - 1];
                        return parse_err("Incomplete comment or key", token_str, line_num)
                    },

                    // Char errors

                    (PS::Rak, Punct::Char) => {
                        let token_str = &s[start_key..=pos - 1];
                        return parse_err("No space after key", token_str, line_num)
                    },

                    // Colon, errors

                    (PS::Fc, Punct::Colon) => {
                        let token_str = &s[start_key..=pos - 1];
                        return parse_err("Colon before key", token_str, line_num)
                    },
                    (PS::Bk, Punct::Colon) => {
                        let token_str = &s[start_key..=pos - 1];
                        return parse_err("Colon before key", token_str, line_num)
                    },
                    (PS::Rak, Punct::Colon) => {
                        let token_str = &s[start_key..=pos - 1];
                        return parse_err("No space after key", token_str, line_num)
                    },

                    // Forward slash errors

                    (PS::Rak, Punct::ForwardSlash) => {
                        let token_str = &s[start_key..=pos - 1];
                        return parse_err("No space after key", token_str, line_num)
                    },
                };  // end match


            }

            match parse_state {

                // Newline, no errors

                PS::Fc => {},
                PS::Bk => {},
                PS::Cm => {},
                PS::Rak => {
                    let token = Token::Key {
                        key:        line[start_key..=end_key].into(),
                        children:   Vec::new(),
                        next:       None,
                        debug:      TokenDebugInfo {line_num},
                    };
                    let indent = indent(
                        &mut root_indent,
                        start_key
                    ).map_err(|err| err.into_bad_indent(line_num))?;
                    builder.append(indent, token)?;
                },
                PS::Ak => {
                    let token = Token::Key {
                        key:        line[start_key..=end_key].into(),
                        children:   Vec::new(),
                        next:       None,
                        debug:      TokenDebugInfo {line_num},
                    };
                    let indent = indent(    
                        &mut root_indent,
                        start_key
                    ).map_err(|err| err.into_bad_indent(line_num))?;
                    builder.append(indent, token)?;
                },
                PS::Iv => {
                    let token = Token::KeyValue {
                        key:    line[start_key..=end_key].into(),
                        value:  line[start_val..=last_pos].into(),
                        next:   None,
                        debug:  TokenDebugInfo {line_num},
                    };
                    let indent = indent(
                        &mut root_indent,
                        start_key
                    ).map_err(|err| err.into_bad_indent(line_num))?;

                    builder.append(indent, token)?;
                },

                // Newline errors

                PS::Cok => {
                    return parse_err("Incomplete line", "/", line_num)
                },
                PS::Ik => {
                    let token_str = &line[start_key..=last_pos - 1];
                    return parse_err("Incomplete line", token_str, line_num)
                },
            };
        };
        match builder.data.is_empty() {
            true => Err(KeyTreeError::ParseNoTokens),
            false => Ok((builder.owned_keytree(), debug_info)),
        }
    }
}

// Returns indent as 0, 1, 2 from token data.
// If the root indent is not set, return 0.
fn indent(root_indent: &mut Option<usize>, start_key: usize) -> Result<usize> {

    match root_indent {
        // root_indent has not been set.
        None => {
            *root_indent = Some(start_key);
            Ok(0)
        },
        Some(root_indent) => {
            let chars_indent = start_key - *root_indent;

            if chars_indent % INDENT_STEP != 0 {
                Err(KeyTreeError::BadIndentTemp(chars_indent))
            } else {
                Ok(chars_indent / INDENT_STEP)
            }
        }
    }
}

fn parse_err<T>(msg: &str, token: &str, line: usize) -> Result<T> {
    Err(KeyTreeError::Parse(msg.to_string(), token.to_string(), line))
}

#[cfg(test)]
pub mod test {

    use super::*;
    use indoc::indoc;
    use crate::KeyTree;
    use crate::{KeyTreeData, TokenDebugInfo};
    use crate::KeyTreeError::BadIndent;
    
    // === indent =================================================================================
    // Complete
    
    #[test]
    fn indent_should_fail_if_key_misaligned() {
        if let Err(e) = indent(&mut Some(0), 3) {
            assert_eq!(e, KeyTreeError::BadIndentTemp(3));
            assert_eq!(e.to_string(), "Bad indent of 3");
        } else { assert!(false) }
    }

    #[test]
    fn indent_should_work() {
        assert_eq!(indent(&mut Some(0), 4).unwrap(), 1);
        assert_eq!(indent(&mut None, 4).unwrap(), 0);
        assert_eq!(indent(&mut Some(0), 8).unwrap(), 2);

        assert_eq!(indent(&mut Some(3), 7).unwrap(), 1);
        assert_eq!(indent(&mut Some(3), 11).unwrap(), 2);
    }

    // === Parser =================================================================================

    #[test]
    fn one_line_key_should_parse() {
        let s = "key:".to_string();
        let kt = Parser::parse_str(&s).unwrap().0;
        assert_eq!(kt.0[0].key(), "key"); 
    }

    #[test]
    fn two_line_should_parse() {
        let s = indoc!("
            key1:
                key2:");
        let kt = Parser::parse_str(&s).unwrap().0;
        assert_eq!(kt.token(0).key(), "key1"); 
        assert_eq!(kt.token(1).key(), "key2");
    }

    #[test]
    fn bad_indent_should_fail() {
        let s = indoc!("
            key:
               key:");
        if let Err(e) = Parser::parse_str(&s) {
           assert_eq!(e, BadIndent(3,2));
        } else { assert!(false) };
    }

    #[test]
    fn child_should_be_set() {
        let s = indoc!("
            key1:
                key2:");
        let kt = Parser::parse_str(&s).unwrap().0;
        assert_eq!(kt.token(0).children()[0], 1);
    }

    #[test]
    fn next_sibling_should_be_set() {
        let s = indoc!("
            key1:
                keyval: a
                keyval: b");
        let kt = Parser::parse_str(&s).unwrap().0;
        assert_eq!(kt.token(1).next(), Some(2));
    }

    // === Builder tests ========================================================================== 
    // Probably complete
    
    fn new_builder() -> Builder {
        let data = KeyTreeData(Vec::new());
        Builder {
            data,
            last_tokens: LastTokens::new(),
            indent: 0,
        }
    }

    fn token_debug_info() -> TokenDebugInfo {
        TokenDebugInfo {line_num: 0}
    }

    fn key_token() -> Token {
        Token::Key {
            key: "key".to_owned(),
            children: Vec::new(),
            next: None,
            debug: token_debug_info(),
        }
    }

    fn keyval_token() -> Token {
        Token::KeyValue {
            key: "key".to_owned(),
            value: "value".to_owned(),
            next: None,
            debug: token_debug_info(),
        }
    }

    #[test]
    fn append_method_should_work() {
        let mut builder = new_builder();
        builder.append(0, key_token()).unwrap();
        assert_eq!(builder.data.0[0], key_token());
    }

    #[test]
    fn append_first_token_should_fail_on_keyvalue() {
        if let Err(err) = new_builder().append_first_token(0, keyval_token()) {
            assert_eq!(err.to_string(), "Expected key found [key: value] on line 1")
        } else { assert!(false) }
    }

    #[test]
    fn append_first_token_should_work() {
        if let Ok(_) = new_builder().append_first_token(0, key_token()) {
            assert!(true)
        } else { assert!(false) }
    }

    #[test]
    fn set_parent_link_should_work() {
        let mut builder = new_builder();
        let old_ix = builder.append_first_token(0, key_token()).unwrap();
        builder.append(1, key_token()).unwrap();
        assert!(builder.data.token(old_ix).children()[0] == 1)
    }

    // === LastTokens tests =======================================================================
    // Complete
    
    #[test] 
    fn last_method_should_work() {
        let mut last = LastTokens::new();
        last.add(0, 0);
        assert_eq!(last.last(0), Some(0));
    }

    #[test]
    fn remove_deeper_than_method_should_work() {
        let mut last = LastTokens::new();
        last.add(0, 0);
        last.add(1, 1);
        last.remove_deeper_than(0);
        assert_eq!(last.0.len(), 1);
    }

    #[test]
    fn replace_last_token_method_should_work() {
        let mut last = LastTokens::new();
        last.add(0, 0);
        last.replace_last_token(0, 1);
        assert_eq!(last.last(0), Some(1));
    }

    #[test]
    fn parent_method_should_work() {

        //  parent:
        //      child1:
        //          grandchild:
        //      child2:

        let mut last = LastTokens::new();
        last.add(0, 0);
        last.add(1, 1);
        last.add(2, 2);

        last.remove_deeper_than(1);
        assert_eq!(last.0.len(), 2);
        last.replace_last_token(1, 3);

        assert_eq!(last.parent(1), 0);
    }

    #[test]
    fn should_not_add_siblings_to_parent() {
        let s = r"
          page:
              country:        Australia
              series:
                  data_type:  u
                  series_id:  AUSURAMS
              series:
                  data_type:  u
                  series_id:  AUSURANAA
        ";
        let kt = Parser::parse_str(&s).unwrap().0;
        assert_eq!(kt.token(0).children(), vec![1, 2]);
    }

    #[test]
    fn should_be_siblings() {
        let s = r"
          key:
              sibling:      sibling1
              sibling:      sibling2
        ";
        let kt = Parser::parse_str(&s).unwrap().0;
        assert_eq!(kt.token(1).next(), Some(2));
    }

    // #[test]
    // fn should_not_add_siblings_to_parent() {
    //     let s = r"
    //       page:
    //           country:        Australia
    //           data_type:      u
    //           index:          0
    //     
    //           series:
    //               data_type:  u
    //               series_id:  AUSURAMS
    //           series:
    //               data_type:  u
    //               series_id:  AUSURANAA
    //     
    //           graphic:
    //               category:   collation
    //               series_id:  AUSURAMS
    //               series_id:  AUSURANAA
    //     ";
    //     let kt = Parser::parse_str(&s).unwrap().0;
    //     assert_eq!(kt.token(0).children(), vec![1, 2, 3, 4, 10]);
    // }

    #[test]
    fn previous_sib_should_work() {
        // key
        //     sibling: sibling1
        let builder = Builder {
            data: KeyTreeData(
                vec![
                    Token::Key {
                        key: "key".to_owned(),
                        children: Vec::new(),
                        next: None,
                        debug: TokenDebugInfo {line_num: 0},
                    },
                    Token::KeyValue {
                        key: "sibling".to_owned(),
                        value: "sibling1".to_owned(),
                        next: None,
                        debug: TokenDebugInfo {line_num: 1},
                    },
                ]
            ),
            last_tokens: LastTokens(vec!(0, 1)),
            indent: 1
        };
        let new_token = Token::KeyValue {
            key: "sibling".to_owned(),
            value: "sibling2".to_owned(),
            next: None,
            debug: TokenDebugInfo {line_num: 2},
        };
        if let Some(ix) = builder.previous_sib_ix(1, &new_token) {
            assert_eq!(ix, 1);
        } else {
            assert!(false)
        }
    }

    #[test]
    fn multiple_keys_should_work() {
        let s = r#"
            seriess:
                series:
                    data_type:          u
                    country:            Australia
                    series_id:          AUSURAMS
                series:
                    data_type:          u
                    country:            Australia
                    series_id:          AUSURANAA
        "#;
        let kt = KeyTree::parse_str(s).unwrap();
        assert_eq!(&kt.data.0[1].next(), &Some(5));
    }
}
