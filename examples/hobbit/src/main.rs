use std::convert::TryInto;
use keytree::{KeyTree, KeyTreeRef};
use keytree::Error;

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

    fn try_into(self) -> Result<Hobbit, Error> {
        Ok(
            Hobbit {
                name:       self.value("hobbit::name")?,
                age:        self.value("hobbit::age")?,
                friends:    self.opt_vec_at("hobbit::friends::hobbit")?,
                nick:       self.opt_value("hobbit::nick")?,
            }
        )
    }
}

fn main() {
    let kt = KeyTree::parse(HOBBITS).unwrap();
    let hobbit: Hobbit = kt.to_ref().try_into().unwrap();

    &dbg!(&hobbit);
}

