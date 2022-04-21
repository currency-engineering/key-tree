# KeyTree

`KeyTree` is a text format designed to convert human readable information into Rust
data-structures.

# Mini-Tutorial

Lets say we have a struct like
```
struct Hobbit {
    name: String,
    age: u32,
    friends: Vec<Hobbit>,
    nick: Option<String>,
}
```
and we want to record in a file how to create an instance of this struct. So we create a string
like
```text
hobbit:
    name:         Frodo Baggins
    age:          60
    friends:
        hobbit:
            name: Bilbo Baggins
            age:  111
        hobbit:
            name: Samwise Gamgee
            age:  38
            nick: Sam
```

Then we need to implement `TryInto<Hobbit>` to deserialize the string into a Rust
data-structure,

```
impl<'a> TryInto<Hobbit> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<Hobbit, Error> {
        Ok(
            Hobbit {

                // use the `from_str` implementation of `String` to get a `name`.
                name: self.from_str("hobbit::name")?,

                // use the `from_str` implementation `u32` to get an `age`.
                age: self.from_str("hobbit::age")?,

                // use the `TryInto<Hobbit> implementation to get a `Vec<Hobbit>`.
                friends: self.opt_vec_at("hobbit::friends::hobbit")?,

                // uses the `from_str` implementation for `String` to get an `Option<String>`.
                // If the keypath does not exist it returns `None`.
                nick: self.opt_from_str("hobbit::nick")?,
            }
        )
    }
}
```

Functions that make a selection from the keytree string and deserialize it are
```
self.at("abc::def::ghi")?
```
```
self.opt_at("abc::def::ghi")?
```
```
self.vec_at("abc::def::ghi")?
```
```
self.opt_vec_at("abc::def::ghi")?
```
```
self.from_str("abc::def::ghi")?
```
```
self.opt_from_str("abc::def::ghi")?
```
```
self.opt_vec_from_str("abc::def::ghi")?
```

The deserializing function should look something like

``` 
    // Creates an 'abstract syntax tree' which is just a set of references into the keytree string s.
    let kt = KeyTree::parse(s).unwrap();

    // kt.to_ref() creates a reference to kt.
    // try_into() does all the deserialization work.
    let hobbit: Hobbit = kt.to_ref().try_into().unwrap();
    &dbg!(&hobbit);

```
## KeyTree Syntax Specification 

- Indentation has meaning and is 4 spaces, relative to the top key. Since indenting is relative
to the top key, then you can neatly align strings embedded in code.

- Each line can be empty, have whitespace only, be a comment, be a key, or be a key/value pair.

- There are keys and values. Key/value pairs look like

```text
name: Frodo
```
Keys have children indented 4 spaces below them. The children can be either keys or key/value pairs.

```text
hobbit:
    name: Frodo
```
hobbit refers to the name of the struct or enum. In this way, the data maps simply to Rust
data-structures.

- If a key has many children with the same key, it forms a collection, for example

```test
hobbit:
    name: Frodo
    name: Bilbo
```
is a collection of hobbits. Sibling keys with the same name must be contiguous. 

- Keys must not include but must be followed by a colon `:`.

- Values are all characters between the combination of ':' and whitespace and the end of the
line. The value is trimmed of whitespace at both ends.

- Comments can only be on their own line. A comment line starts with any amount of whitespace followed by `//`.

```text
// comment
hobbit:
    // another comment
    name: Frodo
```
