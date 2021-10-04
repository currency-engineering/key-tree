//! Convert a `KeyTree` into the Serde data-model. 
//!
//! This crate is requires a feature-gate to compile.

// Take the tokens
//
// The fields of a struct are determined by the token's children.
//
// If the token is a KeyValue then build a struct with a single field.
//
// If the token has a next() build a `seq`.

/// The `Serialize` implementation for `KeyTree` is responsible is responsible for mapping a
/// `KeyTree` into the Serde data-model.

/// The `Serializer` trait is responsible for mapping the Serde data model into a KeyTree. 



/// The implementation of the Serializer type requires a method of each data-model type. 

impl<'a> ser::Serializer for &'a mut Serializer {

    fn serialize_bool(self, v: bool) -> Result<()> {
        self.output += if v { "true" } else { "false" };
        Ok(())
    }
}
