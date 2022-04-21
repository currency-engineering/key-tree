use indoc::indoc;
use keytree::{KeyTree, KeyTreeRef};
use anyhow::Error;

#[derive(Debug)]
struct Plant {
    genus: String
}

impl<'a> TryInto<Plant> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<Plant, Self::Error> {
        Ok(
            Plant {
                species: self.from_str("plant::species")?,
            }
        )
    }
}

#[test]
fn test_first() {
    let s = indoc!("
        plant:
            species:
    ");

    let kt = KeyTree::parse(s, None).unwrap();

    let err: Result<Plant, Error> = kt.to_ref().try_into();

    assert_eq!(err.unwrap_err().to_string(), "Expected keyvalue, found key 'species' on line 2");


}

