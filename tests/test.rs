use std::{
    convert::TryInto,
    error::Error,
};
use key_tree::KeyTree;

static HOBBITS: &'static str = r"hobbit:
    name:         Frodo Baggins
    age:          60
    friends:
        hobbit:
            name: Bilbo Baggins
            age:  111
        hobbit:
            name: Samwise Gamgee
            age:  38
            nick: Sam";

#[derive(Debug)]
#[allow(dead_code)]
struct Hobbit {
    name: String,
    age: u32,
    friends: Vec<Hobbit>,
    nick: Option<String>,
}

impl<'a> TryInto<Hobbit> for KeyTree {
    type Error = Box<dyn Error>;

    fn try_into(self) -> Result<Hobbit, Self::Error> {
        Ok(
            Hobbit {
                name:       self.from_str("hobbit::name")?,
                age:        self.from_str("hobbit::age")?,
                friends:    self.opt_vec_at("hobbit::friends::hobbit")?,
                nick:       self.opt_from_str("hobbit::nick")?,
            }
        )
    }
}

#[test]
fn try_into_should_work() {
    let _: Hobbit = KeyTree::parse_str(HOBBITS)
        .unwrap()
        .try_into()
        .unwrap();
}

