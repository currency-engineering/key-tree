use std::convert::TryInto;
use keytree::{KeyTree, KeyTreeRef};
use err::*;

static HOBBITS: &'static str = r#"hobbit:
    name:         Frodo Baggins
    age:          60
    friends:
        hobbit:
            name: Bilbo Baggins
            age:  111
        hobbit:
            name: Samwise Gamgee
            age:  38
            nick: Sam"#;

#[derive(Debug)]
struct Hobbit {
    name: String,
    age: u32,
    friends: Vec<Hobbit>,
    nick: Option<String>,
}

impl<'a> TryInto<Hobbit> for KeyTreeRef<'a> {
    type Error = Error;

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

fn main() {
    let kt = KeyTree::parse(HOBBITS, None).unwrap();
    let hobbit: Hobbit = kt.to_ref().try_into().unwrap();

    dbg!(&hobbit);
}

