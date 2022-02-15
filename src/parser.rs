#![allow(dead_code)]

use crate::{KeyTree, Token};
use crate::builder::{Parents, SameNameSibs};

use err::*;
use crate::Result;

const INDENT_STEP: usize = 4;

// Parser state. Used in parser() function.
#[derive(Clone, Debug, PartialEq)]
enum PS {
    FC,       // First char.
    BK,       // Before key.
    COK,      // Comment or key
    IK,       // In key.
    RAK,      // The character right after the key.
    AK,       // After key.
    IV,       // In value.
    CM,       // In comment
}

pub struct BadIndent(usize);

impl BadIndent {
    // Maps InnerBadIndent to Error.
    #[allow(unused_variables)]
    fn from_inner(
        self,
        token: &Token,
        line: usize) -> Error
    {
        err!(&format!("Bad indent of {} at line {}.", self.0, line))
    }
}

// Chars received
enum Char  {
    Char, 
    Colon,
    ForwardSlash,
    Newline,
    Whitespace,
}

impl Char {
    fn from_char(c: char) -> Self {
        if c == '\n' { return Char::Newline };
        if c.is_whitespace() { return Char::Whitespace };
        match c {
            ':' => Char::Colon,
            '/' => Char::ForwardSlash,
            _ => Char::Char
        }
    }
}

#[derive(Debug)]
pub (crate) struct Builder<'a> {
    s:              &'a str,
    tokens:         Vec<Token<'a>>,

    // Every token at indent n has a parent at indent 0 to n - 1. This parent
    parents:    Parents,
    snsibs:     SameNameSibs,
}

impl<'a> Builder<'a> {
    pub fn from_str(s: &'a str) -> Self {
        Builder 
         {
            s,
            tokens:     Vec::new(),
            parents:    Parents::new(),
            snsibs:     SameNameSibs::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    pub fn token(&self, ix: usize) -> &Token<'a> {
        &self.tokens[ix]
    }

    // Returns the next() value of ixth token.
    pub fn next(&self, ix: usize) -> Option<usize> {
        self.token(ix).next()
    }

    // Move out of Builder into Core.
    pub fn to_core(self) -> KeyTree<'a> {
        KeyTree(self.tokens)
    }

    // Each token at indent n, except the root token, has parents at each
    // indent level from 0 to n-1. To build up links from parents to children
    // we keep track of current parents. This is akin to thinking about which 
    // parents are 'in scope'. We look at each 

    fn append(&mut self, indent: usize, token: Token<'a>) -> Result<()> {

        match (token, self.is_empty()) {

            (token @ Token::KeyValue {..}, true) => {
                Err(err!(&format!("First token {} must be key.", &token)))
            },

            (token @ Token::Key {..}, true) => {
                self.tokens.push(token);
                self.snsibs.push(0);
                self.parents.push(0);
                Ok(())
            },

            (token, false) => {

                // Possibility A. is that the lastest token (name:) increases
                // the indent level by 1.
                //
                //  hobbit:
                //     name:   Frodo
                
                // Possibility B is that the lastest token (name:) has the same
                // key name and the same indent level as the previous token.
                //
                // hobbit:
                //     name:    Frodo
                //     name:    Bilbo
                
                // Possibility C is that the latest token (location:) has
                // reduced the indent level.
                //
                // scenario:
                //     hobbit:
                //         friends:
                //              ..
                //         name:    Frodo
                //         name:    Bilbo
                //     location:    Middle Earth

                // Remove out-of-scope parents. For example in example 3. we
                // want to remove 'friends:' key as it is no longer in scope.
                self.parents.truncate(indent);

                // Get parent index.
                if indent == 0 {
                    return Err(err!(
                        &format!("Non-root token {} cannot have zero indent at line {}.", &token, token.line())
                    ))
                };

                let parent_ix = match self.parents.parent(indent - 1) {
                    Some(ix) => ix,
                    None => return Err(err!(&format!("Unexpected indent at line {}.", token.line()))),
                };

                // Get the index of the new token, when the token is actually
                // pushed to self.tokens.
                let child_ix = self.tokens.len();
        
                // Append the child of the parent.
                self.tokens[parent_ix].set_child(token.key(), child_ix);

                // If token is a Token::Key then token to parents list.
                if let Token::Key {..} = token {
                    self.parents.push(child_ix);
                }

                // Remove out-of-scope same-name-siblings. For example 'name:'
                // in example 3.
                self.snsibs.truncate(indent + 1);

                // Non-contiguous same-name-siblings will never be found,
                // because keys are discovered by iterating through children
                // Vec in Token, so any repeats will not be found.
                //
                // If a same-name-sibling exists then add next() to it. 
                if let Some(snsib_ix) = self.snsibs.sibling(indent) {
                    if self.tokens[snsib_ix].key() == token.key() {
                        self.tokens[snsib_ix].set_next(child_ix);
                    };
                };

                // Append token to same-name-siblings list.
                self.snsibs.truncate(indent);
                self.snsibs.push(child_ix);

                // Insert token into Builder.
                self.tokens.push(token);

                Ok(())
            },
        }
    }

    // Parse a `KeyTree` string into an immutable `KeyTreeCore`. For context, see
    // main example at the start of the documentation or in README.md
    pub fn parse(s: &str) -> Result<KeyTree> {

        if s == "" { return Err(err!("Empty string.")) };

        let mut parse_state: PS = PS::FC;

        let mut line            = 0;
        let mut line_start      = 0;
        let mut start_key       = 0;
        let mut end_key         = 0;
        let mut start_val       = 0;
        // let mut end_val;
        let mut root_indent     = None;

        let mut core_builder: Builder = Builder::from_str(s);

        for (pos, ch) in core_builder.s.char_indices() {

            match (&parse_state, Char::from_char(ch)) {

                // Matches are ordered by estimated rate of occurence.

                // Whitespace, no errors.

                (PS::FC, Char::Whitespace) => {
                    line_start = pos;
                    parse_state = PS::BK;
                },
                (PS::BK, Char::Whitespace) => { },
                (PS::CM, Char::Whitespace) => { },
                (PS::RAK, Char::Whitespace) => {
                    parse_state = PS::AK;
                },
                (PS::AK, Char::Whitespace) => { },
                (PS::IV, Char::Whitespace) => { },

                // Char, no errors.

                (PS::AK, Char::Char) => {
                    start_val = pos;
                    parse_state = PS::IV;
                },
                (PS::IV, Char::Char) => {},
                (PS::FC, Char::Newline) => {
                    line += 1;
                    parse_state = PS::FC;
                },
                (PS::FC, Char::Char) => {
                    line_start = pos;
                    start_key = pos;
                    parse_state = PS::IK;
                },
                (PS::BK, Char::Char) => {
                    start_key = pos;
                    parse_state = PS::IK;
                },
                (PS::COK, Char::Char) => {
                    parse_state = PS::IK;
                },
                (PS::CM, Char::Char) => { },
                (PS::IK, Char::Char) => {}

                // Newline, no errors

                (PS::BK, Char::Newline) => {
                    line += 1;
                    parse_state = PS::FC;
                },
                (PS::CM, Char::Newline) => {
                    line += 1;
                    parse_state = PS::FC;
                },

                (PS::RAK, Char::Newline) => {
                    line += 1;
                    let token = Token::Key {
                        key:        &s[start_key..=end_key],
                        children:   Vec::new(),
                        next:       None,
                        line:       line,
                    };
                    let indent = indent(
                        &mut root_indent,
                        line_start,
                        start_key
                    ).map_err(|err| err.from_inner(&token, line))?;
                    core_builder.append(indent, token)?;
                    parse_state = PS::FC;
                },

                (PS::AK, Char::Newline) => {
                    line += 1;
                    let token = Token::Key {
                        key:        &s[start_key..=end_key],
                        children:   Vec::new(),
                        next:       None,
                        line:       line,
                    };
                    let indent = indent(    
                        &mut root_indent,
                        line_start,
                        start_key
                    ).map_err(|e| e.from_inner(&token, line))?;
                    core_builder.append(indent, token)?;
                    parse_state = PS::FC;
                },
                (PS::IV, Char::Newline) => {
                    line += 1;
                    let token = Token::KeyValue {
                        key:    &s[start_key..=end_key],
                        value:  &s[start_val..=pos - 1],
                        next:   None,
                        line:   line,
                    };
                    let indent = indent(
                        &mut root_indent,
                        line_start,
                        start_key
                    ).map_err(|e| e.from_inner(&token, line))?;

                    core_builder.append(indent, token)?;
                    parse_state = PS::FC;
                },

                // Colon, no errors

                (PS::COK, Char::Colon) => {
                    parse_state = PS::IK;
                },
                (PS::CM, Char::Colon) => { },
                (PS::IV, Char::Colon) => {},
                (PS::AK, Char::Colon) => {
                    start_val = pos;
                    parse_state = PS::IV;
                },
                (PS::IK, Char::Colon) => {
                    end_key = pos - 1;
                    parse_state = PS::RAK;
                }

                // Forward slash, no errors


                (PS::COK, Char::ForwardSlash) => {
                    parse_state = PS::CM;
                },
                (PS::FC, Char::ForwardSlash) => {
                    line_start = pos;
                    start_key = pos;
                    parse_state = PS::COK;
                },
                (PS::CM, Char::ForwardSlash) => {},
                (PS::BK, Char::ForwardSlash) => {
                    start_key = pos;
                    parse_state = PS::COK;
                },
                (PS::IK, Char::ForwardSlash) => {}
                (PS::AK, Char::ForwardSlash) => {
                    start_val = pos;
                    parse_state = PS::IV;
                },
                (PS::IV, Char::ForwardSlash) => {},

                // Whitespace errors

                (PS::IK, Char::Whitespace) => {
                    let token_str = &s[start_key..=pos - 1];
                    return Err(
                        err!(&format!("No colon after key {} at line {}.", &token_str, line + 1))
                    )
                },
                (PS::COK, Char::Whitespace) => {
                    let token_str = &s[start_key..=pos - 1];
                    return Err(
                        err!(&format!("Incomplete comment of key {} at {}.", &token_str, line + 1))
                    )
                },

                // Char errors

                (PS::RAK, Char::Char) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(
                        err!(&format!("No space after key {} at line {}.", &token_str, line))
                    )
                },

                // Newline errors

                (PS::COK, Char::Newline) => {
                    line += 1;
                    return Err(
                        err!(&format!("Incomplete line {} at {}.", &String::from("/"), line))
                    )
                },
                (PS::IK, Char::Newline) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(err!(&format!("Incomplete line {} at {}.", &token_str, line)))
                },

                // Colon, errors

                (PS::FC, Char::Colon) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(err!(&format!("Colon before key {} at {}.", &token_str, line)))
                },
                (PS::BK, Char::Colon) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(err!(&format!("Colon before key {} at {}.", &token_str, line)))
                },
                (PS::RAK, Char::Colon) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(err!(&format!("No space after key {} at {}.", &token_str, line)))
                },

                // Forward slash errors

                (PS::RAK, Char::ForwardSlash) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(err!(&format!("No space after key {} at line {}.", &token_str, line)))
                },
            };  // end match
            
        };

        // Handle strings that don't end in '\n".

        match parse_state {
            PS::FC => {},
            PS::BK => {},
            PS::COK => {
                let token_str = &s[start_key..];
                return Err(err!(&format!("Incomplete comment or key {} at line {}.", &token_str, line)))
            },
            PS::IK => { 
                line += 1;
                let token_str = &s[start_key..];
                return Err(err!(&format!("Incomplete line {} at {}.", &token_str, line)))
            },
            PS::RAK => {
                line += 1;
                let token = Token::Key {
                    key: &s[start_key..s.chars().count() - 1],
                    children: Vec::new(),
                    next: None,
                    line: line,
                };
                let indent = indent(
                    &mut root_indent,
                    line_start,
                    start_key
                ).map_err(|e| e.from_inner(&token, line))?;
                core_builder.append(indent, token)?;
            },
            PS::AK => {
                line += 1;
                let token = Token::Key {
                    key:        &s[start_key..],
                    children:   Vec::new(),
                    next:       None,
                    line:       line,
                };
                let indent = indent(
                    &mut root_indent,
                    line_start,
                    start_key
                ).map_err(|e| e.from_inner(&token, line))?;
                core_builder.append(indent, token)?;
            },
            PS::IV => {
                line += 1;
                let token = Token::KeyValue {
                    key: &s[start_key..=end_key],
                    value: &s[start_val..],
                    next: None,
                    line: line,
                };
                let indent = indent(
                    &mut root_indent,
                    line_start,
                    start_key
                ).map_err(|e| e.from_inner(&token, line))?;
                core_builder.append(indent, token)?;
            },
            PS::CM => {},
        };

        match core_builder.is_empty() {
            true => Err(err!("No tokens")),
            false => Ok(core_builder.to_core()),
        }
    }
}

// Returns indent as 0, 1, 2 from token data.
fn indent(
    root_indent:    &mut Option<usize>,
    line_start:     usize,
    start_key:      usize) -> std::result::Result<usize, BadIndent>
{
    match root_indent {

        // root_indent has not been set.
        None => {
            *root_indent = Some(start_key - line_start);
            Ok(0)
        },
        Some(root_indent) => {
            let chars_indent = start_key -
                line_start -
                *root_indent;

            if chars_indent % INDENT_STEP != 0 {
                return Err(BadIndent(chars_indent))
            } else {
                Ok(chars_indent / INDENT_STEP)
            }
        }
    }
}

