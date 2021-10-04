//! Conversions from the value of a key/value pair.
//!
//! Conversions can be implemented by the client.
//! `from_str` is a helper function that takes a description
//! of the type being converted into, for use  in error
//! messages.
//!
//! ```
//! impl<'a> TryInto<f32> for KeyTreeRef<'a> {
//!     type Error = Error;
//! 
//!     fn try_into(self) -> Result<f32> {
//!         self.from_str("f32")
//!     }
//! }
//! ```

use core::convert::TryInto;
use core::num::{  
    NonZeroI128,
    NonZeroI16,
    NonZeroI32,
    NonZeroI64,
    NonZeroI8,
    NonZeroIsize,
    NonZeroU128,
    NonZeroU16,
    NonZeroU32,
    NonZeroU64,
    NonZeroU8,
    NonZeroUsize,
};

use crate::{KeyTreeRef, Token};
use crate::error::{Error, ErrorKind};
use crate::Result;

// use std::iter::FromIterator;
use std::net::{
    IpAddr,
    Ipv4Addr,
    Ipv6Addr,
    SocketAddr,
    SocketAddrV4,
    SocketAddrV6,
};
use std::path::PathBuf;
use std::str::FromStr;

impl<'a> KeyTreeRef<'a> {
    pub fn from_str<T: FromStr>(&self, into_type: &str) -> Result<T> {
        match self.top_token() {
            Token::KeyValue {
                next,
                value,
                ..
            } => {
               match next {
                    Some(i) => Err(Error::new(ErrorKind::EUniqueKeyValueFMany(String::from("todo"), *i))),
                    None => {
                        match T::from_str(value) {
                            Err(_) => {
                                Err(Error::new(ErrorKind::FailedFromStr(
                                    self.top_token().to_string(),
                                    self.top_token().line().to_string(),
                                    into_type.to_string(),
                                )))
                            },
                            Ok(t) => Ok(t),
                        }
                    }
                }
            },
            Token::Key { .. } => Err(Error::new(ErrorKind::EKeyValueFKey)),
        }
    }
}


impl<'a> TryInto<IpAddr> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<IpAddr> {
        self.from_str("IP address")
    }
}

impl<'a> TryInto<SocketAddr> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<SocketAddr> {
        self.from_str("socket address")
    }
}

impl<'a> TryInto<bool> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<bool> {
        self.from_str("bool")
    }
}

impl<'a> TryInto<char> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<char> {
        self.from_str("char")
    }
}

impl<'a> TryInto<f32> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<f32> {
        self.from_str("f32")
    }
}

impl<'a> TryInto<f64> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<f64> {
        self.from_str("f64")
    }
}

impl<'a> TryInto<i128> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<i128> {
        self.from_str("i128")
    }
}

impl<'a> TryInto<i16> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<i16> {
        self.from_str("i16")
    }
}

impl<'a> TryInto<i32> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<i32> {
        self.from_str("i32")
    }
}

impl<'a> TryInto<i64> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<i64> {
        self.from_str("i64")
    }
}

impl<'a> TryInto<i8> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<i8> {
        self.from_str("i8")
    }
}

impl<'a> TryInto<isize> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<isize> {
        self.from_str("isize")
    }
}

impl<'a> TryInto<u128> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<u128> {
        self.from_str("u128")
    }
}

impl<'a> TryInto<u16> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<u16> {
        self.from_str("u16")
    }
}

impl<'a> TryInto<u32> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<u32> {
        self.from_str("u32")
    }
}

impl<'a> TryInto<u64> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<u64> {
        self.from_str("u64")
    }
}

impl<'a> TryInto<u8> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<u8> {
        self.from_str("u8")
    }
}

impl<'a> TryInto<usize> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<usize> {
        self.from_str("usize")
    }
}

impl<'a> TryInto<Ipv4Addr> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<Ipv4Addr> {
        self.from_str("IPv4 address")
    }
}

impl<'a> TryInto<Ipv6Addr> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<Ipv6Addr> {
        self.from_str("IPv6 address")
    }
}

impl<'a> TryInto<SocketAddrV4> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<SocketAddrV4> {
        self.from_str("IPv4 address")
    }
}

impl<'a> TryInto<SocketAddrV6> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<SocketAddrV6> {
        self.from_str("IPv6 address")
    }
}

impl<'a> TryInto<NonZeroI128> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroI128> {
        self.from_str("non-zero i128")
    }
}

impl<'a> TryInto<NonZeroI16> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroI16> {
        self.from_str("non-zero i16")
    }
}

impl<'a> TryInto<NonZeroI32> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroI32> {
        self.from_str("non-zero i32")
    }
}

impl<'a> TryInto<NonZeroI64> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroI64> {
        self.from_str("non-zero i64")
    }
}


impl<'a> TryInto<NonZeroI8> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroI8> {
        self.from_str("non-zero i8")
    }
}

impl<'a> TryInto<NonZeroIsize> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroIsize> {
        self.from_str("non-zero isize")
    }
}

impl<'a> TryInto<NonZeroU128> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroU128> {
        self.from_str("non-zero u128")
    }
}

impl<'a> TryInto<NonZeroU16> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroU16> {
        self.from_str("non-zero u16")
    }
}

impl<'a> TryInto<NonZeroU32> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroU32> {
        self.from_str("non-zero u32")
    }
}

impl<'a> TryInto<NonZeroU64> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroU64> {
        self.from_str("non-zero u64")
    }
}

impl<'a> TryInto<NonZeroU8> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroU8> {
        self.from_str("non-zero u8")
    }
}

impl<'a> TryInto<NonZeroUsize> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<NonZeroUsize> {
        self.from_str("non-zero usize")
    }
}

impl<'a> TryInto<PathBuf> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<PathBuf> {
        self.from_str("path")
    }
}

impl<'a> TryInto<String> for KeyTreeRef<'a> {
    type Error = Error;

    fn try_into(self) -> Result<String> {
        self.from_str("string")
    }
}

