#![allow(dead_code)]

use anyhow::{anyhow, Error, Result};
use crate::{builder::{Parents, SameNameSibs}, KeyTree, Token};
use std::path::{Path, PathBuf};

const INDENT_STEP: usize = 4;

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

pub struct BadIndent(usize);

impl BadIndent {
    // Maps InnerBadIndent to Error.
    #[allow(unused_variables)]
    fn from_inner(
        self,
        token: &Token,
        line: usize) -> Error
    {
        anyhow!(format!("Bad indent of {} at line {}.", self.0, line))
    }
}

// Chars received
enum Punct  {
    Char, 
    Colon,
    ForwardSlash,
    Newline,
    Whitespace,
}

impl Punct {
    fn from_char(c: char) -> Self {
        if c == '\n' { return Punct::Newline };
        if c.is_whitespace() { return Punct::Whitespace };
        match c {
            ':' => Punct::Colon,
            '/' => Punct::ForwardSlash,
            _ => Punct::Char
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
    filename:   Option<PathBuf>
}

impl<'a> Builder<'a> {
    fn from_str(s: &'a str, filename: Option<&Path>) -> Self {
        Builder {
            s,
            tokens:     Vec::new(),
            parents:    Parents::new(),
            snsibs:     SameNameSibs::new(),
            filename:   filename.map(|path| path.to_path_buf()),
        }
    }

    fn is_empty(&self) -> bool { self.tokens.is_empty() }

    fn token(&self, ix: usize) -> &Token<'a> { &self.tokens[ix] }

    // Returns the next() value of ixth token.
    fn next(&self, ix: usize) -> Option<usize> { self.token(ix).next() }

    // Move out of Builder into Core.
    fn to_core(self) -> KeyTree<'a> {
        KeyTree {
            tokens: self.tokens,
            filename: self.filename,
        }
    }

    // Each token at indent n, except the root token, has parents at each
    // indent level from 0 to n-1. To build up links from parents to children
    // we keep track of current parents. This is akin to thinking about which 
    // parents are 'in scope'. We look at each 

    fn append(&mut self, indent: usize, token: Token<'a>) -> Result<()> {

        match (token, self.is_empty()) {

            (token @ Token::KeyValue {..}, true) => {
                Err(anyhow!(format!("First token {} must be key.", &token)))
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
                    return Err(anyhow!(
                        format!("Non-root token {} cannot have zero indent at line {}.", &token, token.line())
                    ))
                };

                let parent_ix = match self.parents.parent(indent - 1) {
                    Some(ix) => ix,
                    None => return Err(anyhow!(format!("Unexpected indent at line {}.", token.line()))),
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

    // Parse a string into a `KeyTree`. If there is a filename, this can be input for error
    // handling. 
    pub fn parse(s: &'a str, f: Option<&Path>) -> Result<KeyTree<'a>> {

        if s.is_empty() { return Err(anyhow!("Empty string.")) };

        let mut parse_state: PS = PS::Fc;

        let mut line            = 0;
        let mut line_start      = 0;
        let mut start_key       = 0;
        let mut end_key         = 0;
        let mut start_val       = 0;
        // let mut end_val;
        let mut root_indent     = None;

        let mut core_builder: Builder = Builder::from_str(s, f);

        for (pos, ch) in core_builder.s.char_indices() {

            match (&parse_state, Punct::from_char(ch)) {

                // Matches are ordered by estimated rate of occurence.

                // Whitespace, no errors.

                (PS::Fc, Punct::Whitespace) => {
                    line_start = pos;
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
                (PS::Fc, Punct::Newline) => {
                    line += 1;
                    parse_state = PS::Fc;
                },
                (PS::Fc, Punct::Char) => {
                    line_start = pos;
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

                // Newline, no errors

                (PS::Bk, Punct::Newline) => {
                    line += 1;
                    parse_state = PS::Fc;
                },
                (PS::Cm, Punct::Newline) => {
                    line += 1;
                    parse_state = PS::Fc;
                },

                (PS::Rak, Punct::Newline) => {
                    line += 1;
                    let token = Token::Key {
                        key:        &s[start_key..=end_key],
                        children:   Vec::new(),
                        next:       None,
                        line,
                    };
                    let indent = indent(
                        &mut root_indent,
                        line_start,
                        start_key
                    ).map_err(|err| err.from_inner(&token, line))?;
                    core_builder.append(indent, token)?;
                    parse_state = PS::Fc;
                },

                (PS::Ak, Punct::Newline) => {
                    line += 1;
                    let token = Token::Key {
                        key:        &s[start_key..=end_key],
                        children:   Vec::new(),
                        next:       None,
                        line,
                    };
                    let indent = indent(    
                        &mut root_indent,
                        line_start,
                        start_key
                    ).map_err(|e| e.from_inner(&token, line))?;
                    core_builder.append(indent, token)?;
                    parse_state = PS::Fc;
                },
                (PS::Iv, Punct::Newline) => {
                    line += 1;
                    let token = Token::KeyValue {
                        key:    &s[start_key..=end_key],
                        value:  &s[start_val..=pos - 1],
                        next:   None,
                        line,
                    };
                    let indent = indent(
                        &mut root_indent,
                        line_start,
                        start_key
                    ).map_err(|e| e.from_inner(&token, line))?;

                    core_builder.append(indent, token)?;
                    parse_state = PS::Fc;
                },

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
                    line_start = pos;
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
                    return Err(
                        anyhow!(format!("No colon after key {} at line {}.", &token_str, line + 1))
                    )
                },
                (PS::Cok, Punct::Whitespace) => {
                    let token_str = &s[start_key..=pos - 1];
                    return Err(
                        anyhow!(format!("Incomplete comment of key {} at {}.", &token_str, line + 1))
                    )
                },

                // Char errors

                (PS::Rak, Punct::Char) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(
                        anyhow!(format!("No space after key {} at line {}.", &token_str, line))
                    )
                },

                // Newline errors

                (PS::Cok, Punct::Newline) => {
                    line += 1;
                    return Err(
                        anyhow!(format!("Incomplete line {} at {}.", &String::from("/"), line))
                    )
                },
                (PS::Ik, Punct::Newline) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(anyhow!(format!("Incomplete line {} at {}.", &token_str, line)))
                },

                // Colon, errors

                (PS::Fc, Punct::Colon) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(anyhow!(format!("Colon before key {} at {}.", &token_str, line)))
                },
                (PS::Bk, Punct::Colon) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(anyhow!(format!("Colon before key {} at {}.", &token_str, line)))
                },
                (PS::Rak, Punct::Colon) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(anyhow!(format!("No space after key {} at {}.", &token_str, line)))
                },

                // Forward slash errors

                (PS::Rak, Punct::ForwardSlash) => {
                    line += 1;
                    let token_str = &s[start_key..=pos - 1];
                    return Err(anyhow!(format!("No space after key {} at line {}.", &token_str, line)))
                },
            };  // end match
            
        };

        // Handle strings that don't end in '\n".

        match parse_state {
            PS::Fc => {},
            PS::Bk => {},
            PS::Cok => {
                let token_str = &s[start_key..];
                return Err(anyhow!(format!("Incomplete comment or key {} at line {}.", &token_str, line)))
            },
            PS::Ik => { 
                line += 1;
                let token_str = &s[start_key..];
                return Err(anyhow!(format!("Incomplete line {} at {}.", &token_str, line)))
            },
            PS::Rak => {
                line += 1;
                let token = Token::Key {
                    key: &s[start_key..s.chars().count() - 1],
                    children: Vec::new(),
                    next: None,
                    line,
                };
                let indent = indent(
                    &mut root_indent,
                    line_start,
                    start_key
                ).map_err(|e| e.from_inner(&token, line))?;
                core_builder.append(indent, token)?;
            },
            PS::Ak => {
                line += 1;
                let token = Token::Key {
                    key:        &s[start_key..],
                    children:   Vec::new(),
                    next:       None,
                    line,
                };
                let indent = indent(
                    &mut root_indent,
                    line_start,
                    start_key
                ).map_err(|e| e.from_inner(&token, line))?;
                core_builder.append(indent, token)?;
            },
            PS::Iv => {
                line += 1;
                let token = Token::KeyValue {
                    key: &s[start_key..=end_key],
                    value: &s[start_val..],
                    next: None,
                    line,
                };
                let indent = indent(
                    &mut root_indent,
                    line_start,
                    start_key
                ).map_err(|e| e.from_inner(&token, line))?;
                core_builder.append(indent, token)?;
            },
            PS::Cm => {},
        };

        match core_builder.is_empty() {
            true => Err(anyhow!("No tokens")),
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
                Err(BadIndent(chars_indent))
            } else {
                Ok(chars_indent / INDENT_STEP)
            }
        }
    }
}

