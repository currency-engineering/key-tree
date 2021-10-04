
// Keeps track of the last token at each indent level. These parents 
// can be thought of as 'in scope'.
#[derive(Debug)]
pub (crate) struct Parents(pub Vec<usize>);

impl Parents {
    pub fn new() -> Self {
        Parents(Vec::new())
    }

    pub fn parent(&self, indent: usize) -> Option<usize> {
        if indent >= self.0.len() {
            None
        } else {
            Some(self.0[indent])
        }
    }

    pub fn truncate(&mut self, len: usize) {
        self.0.truncate(len)
    }

    pub fn push(&mut self, token_i: usize) {
        self.0.push(token_i);
    }
}

// Same-Name-Siblings. Keeps track of siblings with the same keys.
#[derive(Debug)]
pub (crate) struct SameNameSibs(pub Vec<usize>);

impl SameNameSibs {
    pub fn new() -> Self {
        SameNameSibs(Vec::new())
    }

    pub fn sibling(&self, indent: usize) -> Option<usize> {
        match self.0.len() > indent {
            true => Some(self.0[indent]),
            false => None,
        }
    }

    pub fn truncate(&mut self, len: usize) {
        self.0.truncate(len)
    }

    pub fn push(&mut self, token_ix: usize) {
        self.0.push(token_ix);
    }
}
