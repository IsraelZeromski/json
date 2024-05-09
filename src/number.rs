use crate::de::ParserNumber;
use crate::error::Error;
#[cfg(feature = "arbitrary_precision")]
use crate::error::ErrorCode;
#[cfg(feature = "arbitrary_precision")]
use alloc::borrow::ToOwned;
#[cfg(feature = "arbitrary_precision")]
use alloc::string::{String, ToString};
use core::fmt::{self, Debug, Display};
#[cfg(not(feature = "arbitrary_precision"))]
use core::hash::{Hash, Hasher};
use serde::de::{self, Unexpected, Visitor};
#[cfg(feature = "arbitrary_precision")]
use serde::de::{IntoDeserializer, MapAccess};
use serde::{forward_to_deserialize_any, Deserialize, Deserializer, Serialize, Serializer};

#[cfg(feature = "arbitrary_precision")]
pub(crate) const TOKEN: &str = "$serde_json::private::Number";

/// Represents a JSON number, whether integer or floating point.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Number {
    n: N,
}

#[cfg(not(feature = "arbitrary_precision"))]
#[derive(Copy, Clone)]
enum N {
    PosInt(u64),
    /// Always less than zero.
    NegInt(i64),
    /// Always finite.
    PosInt128(u128),
    /// Always less than zero.
    NegInt128(i128),
    Float(f64),
}

#[cfg(not(feature = "arbitrary_precision"))]
impl PartialEq for N {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (N::PosInt(a), N::PosInt(b)) => a == b,
            (N::NegInt(a), N::NegInt(b)) => a == b,
            (N::PosInt128(a), N::PosInt128(b)) => a == b,
            (N::NegInt128(a), N::NegInt128(b)) => a == b,
            (N::Float(a), N::Float(b)) => a == b,
            _ => false,
        }
    }
}

// Implementing Eq is fine since any float values are always finite.
#[cfg(not(feature = "arbitrary_precision"))]
impl Eq for N {}

#[cfg(not(feature = "arbitrary_precision"))]
impl Hash for N {
    fn hash<H: Hasher>(&self, h: &mut H) {
        match *self {
            N::PosInt(i) => i.hash(h),
            N::NegInt(i) => i.hash(h),
            N::PosInt128(i) => i.hash(h),
            N::NegInt128(i) => i.hash(h),
            N::Float(f) => {
                if f == 0.0f64 {
                    // There are 2 zero representations, +0 and -0, which
                    // compare equal but have different bits. We use the +0 hash
                    // for both so that hash(+0) == hash(-0).
                    0.0f64.to_bits().hash(h);
                } else {
                    f.to_bits().hash(h);
                }
            }
        }
    }
}

#[cfg(feature = "arbitrary_precision")]
type N = String;

impl Number {
    /// Returns true if the `Number` is an integer between `i64::MIN` and
    /// `i64::MAX`.
    ///
    /// For any Number on which `is_i64` returns true, `as_i64` is guaranteed to
    /// return the integer value.
    ///
    /// ```
    /// # use serde_json::json;
    /// #
    /// let big = i64::MAX as u64 + 10;
    /// let v = json!({ "a": 64, "b": big, "c": 256.0 });
    ///
    /// assert!(v["a"].is_i64());
    ///
    /// // Greater than i64::MAX.
    /// assert!(!v["b"].is_i64());
    ///
    /// // Numbers with a decimal point are not considered integers.
    /// assert!(!v["c"].is_i64());
    /// ```
    #[inline]
    pub fn is_i64(&self) -> bool {
        #[cfg(not(feature = "arbitrary_precision"))]
        match self.n {
            N::PosInt(v) => v <= i64::MAX as u64,
            N::PosInt128(v) => v <= i128::max_value() as u128,
            N::NegInt(_) | N::NegInt128(_) => true,
            N::Float(_) => false,
        }
        #[cfg(feature = "arbitrary_precision")]
        self.as_i64().is_some()
    }

    /// Returns true if the `Number` is an integer between zero and `u64::MAX`.
    ///
    /// For any Number on which `is_u64` returns true, `as_u64` is guaranteed to
    /// return the integer value.
    ///
    /// ```
    /// # use serde_json::json;
    /// #
    /// let v = json!({ "a": 64, "b": -64, "c": 256.0 });
    ///
    /// assert!(v["a"].is_u64());
    ///
    /// // Negative integer.
    /// assert!(!v["b"].is_u64());
    ///
    /// // Numbers with a decimal point are not considered integers.
    /// assert!(!v["c"].is_u64());
    /// ```
    #[inline]
    pub fn is_u64(&self) -> bool {
        #[cfg(not(feature = "arbitrary_precision"))]
        match self.n {
            N::PosInt(_) => true,
            N::NegInt(_) | N::Float(_) => false,
            _ => false,
        }
        #[cfg(feature = "arbitrary_precision")]
        self.as_u64().is_some()
    }

    /// Returns true if the `Number` can be represented by f64.
    ///
    /// For any Number on which `is_f64` returns true, `as_f64` is guaranteed to
    /// return the floating point value.
    ///
    /// Currently this function returns true if and only if both `is_i64` and
    /// `is_u64` return false but this is not a guarantee in the future.
    ///
    /// ```
    /// # use serde_json::json;
    /// #
    /// let v = json!({ "a": 256.0, "b": 64, "c": -64 });
    ///
    /// assert!(v["a"].is_f64());
    ///
    /// // Integers.
    /// assert!(!v["b"].is_f64());
    /// assert!(!v["c"].is_f64());
    /// ```
    #[inline]
    pub fn is_f64(&self) -> bool {
        #[cfg(not(feature = "arbitrary_precision"))]
        match self.n {
            N::Float(_) => true,
            N::PosInt(_) | N::NegInt(_) => false,
            _ => false,
        }
        #[cfg(feature = "arbitrary_precision")]
        {
            for c in self.n.chars() {
                if c == '.' || c == 'e' || c == 'E' {
                    return self.n.parse::<f64>().ok().map_or(false, f64::is_finite);
                }
            }
            false
        }
    }

    /// If the `Number` is an integer, represent it as i64 if possible. Returns
    /// None otherwise.
    ///
    /// ```
    /// # use serde_json::json;
    /// #
    /// let big = i64::MAX as u64 + 10;
    /// let v = json!({ "a": 64, "b": big, "c": 256.0 });
    ///
    /// assert_eq!(v["a"].as_i64(), Some(64));
    /// assert_eq!(v["b"].as_i64(), None);
    /// assert_eq!(v["c"].as_i64(), None);
    /// ```
    #[inline]
    pub fn as_i64(&self) -> Option<i64> {
        #[cfg(not(feature = "arbitrary_precision"))]
        match self.n {
            N::PosInt(n) => {
                if n <= i64::MAX as u64 {
                    Some(n as i64)
                } else {
                    None
                }
            }
            N::NegInt(n) => Some(n),
            N::Float(_) => None,
            _ => None,
        }
        #[cfg(feature = "arbitrary_precision")]
        self.n.parse().ok()
    }

    /// If the `Number` is an integer, represent it as i128 if possible. Returns
    /// None otherwise.
    ///
    /// ```
    /// # use serde_json::json;
    /// #
    /// let big = i128::MAX as u128 + 10;
    /// let v = json!({ "a": 64, "b": big, "c": 256.0 });
    ///
    /// assert_eq!(v["a"].as_i128(), Some(64));
    /// assert_eq!(v["b"].as_i128(), None);
    /// assert_eq!(v["c"].as_i128(), None);
    /// ```
    #[inline]
    pub fn as_i128(&self) -> Option<i128> {
        #[cfg(not(feature = "arbitrary_precision"))]
        match self.n {
            N::PosInt128(n) => {
                if n <= i128::MAX as u128 {
                    Some(n as i128)
                } else {
                    None
                }
            }
            N::NegInt128(n) => Some(n),
            N::PosInt(n) => {
                if n <= i64::MAX as u64 {
                    Some(n.into())
                } else {
                    None
                }
            }
            N::NegInt(n) => Some(n.into()),
            N::Float(_) => None,
        }
        #[cfg(feature = "arbitrary_precision")]
        self.n.parse().ok()
    }

    /// If the `Number` is an integer, represent it as u64 if possible. Returns
    /// None otherwise.
    ///
    /// ```
    /// # use serde_json::json;
    /// #
    /// let v = json!({ "a": 64, "b": -64, "c": 256.0 });
    ///
    /// assert_eq!(v["a"].as_u64(), Some(64));
    /// assert_eq!(v["b"].as_u64(), None);
    /// assert_eq!(v["c"].as_u64(), None);
    /// ```
    #[inline]
    pub fn as_u64(&self) -> Option<u64> {
        #[cfg(not(feature = "arbitrary_precision"))]
        match self.n {
            N::PosInt(n) => Some(n),
            N::NegInt(_) | N::Float(_) => None,
            _ => None,
        }
        #[cfg(feature = "arbitrary_precision")]
        self.n.parse().ok()
    }

    /// If the `Number` is an integer, represent it as u128 if possible. Returns
    /// None otherwise.
    ///
    /// ```
    /// # use serde_json::json;
    /// #
    /// let v = json!({ "a": 64, "b": -64, "c": 256.0 });
    ///
    /// assert_eq!(v["a"].as_u128(), Some(64));
    /// assert_eq!(v["b"].as_u128(), None);
    /// assert_eq!(v["c"].as_u128(), None);
    /// ```
    #[inline]
    pub fn as_u128(&self) -> Option<u128> {
        #[cfg(not(feature = "arbitrary_precision"))]
        match self.n {
            N::PosInt128(n) => Some(n),
            N::PosInt(n) => Some(n.into()),
            _ => None,
        }
        #[cfg(feature = "arbitrary_precision")]
        self.n.parse().ok()
    }

    /// Represents the number as f64 if possible. Returns None otherwise.
    ///
    /// ```
    /// # use serde_json::json;
    /// #
    /// let v = json!({ "a": 256.0, "b": 64, "c": -64 });
    ///
    /// assert_eq!(v["a"].as_f64(), Some(256.0));
    /// assert_eq!(v["b"].as_f64(), Some(64.0));
    /// assert_eq!(v["c"].as_f64(), Some(-64.0));
    /// ```
    #[inline]
    pub fn as_f64(&self) -> Option<f64> {
        #[cfg(not(feature = "arbitrary_precision"))]
        match self.n {
            N::PosInt(n) => Some(n as f64),
            N::NegInt(n) => Some(n as f64),
            N::Float(n) => Some(n),
            _ => None,
        }
        #[cfg(feature = "arbitrary_precision")]
        self.n.parse::<f64>().ok().filter(|float| float.is_finite())
    }

    /// Converts a finite `f64` to a `Number`. Infinite or NaN values are not JSON
    /// numbers.
    ///
    /// ```
    /// # use std::f64;
    /// #
    /// # use serde_json::Number;
    /// #
    /// assert!(Number::from_f64(256.0).is_some());
    ///
    /// assert!(Number::from_f64(f64::NAN).is_none());
    /// ```
    #[inline]
    pub fn from_f64(f: f64) -> Option<Number> {
        if f.is_finite() {
            let n = {
                #[cfg(not(feature = "arbitrary_precision"))]
                {
                    N::Float(f)
                }
                #[cfg(feature = "arbitrary_precision")]
                {
                    ryu::Buffer::new().format_finite(f).to_owned()
                }
            };
            Some(Number { n })
        } else {
            None
        }
    }

    /// Returns the exact original JSON representation that this Number was
    /// parsed from.
    ///
    /// For numbers constructed not via parsing, such as by `From<i32>`, returns
    /// the JSON representation that serde\_json would serialize for this
    /// number.
    ///
    /// ```
    /// # use serde_json::Number;
    /// for value in [
    ///     "7",
    ///     "12.34",
    ///     "34e-56789",
    ///     "0.0123456789000000012345678900000001234567890000123456789",
    ///     "343412345678910111213141516171819202122232425262728293034",
    ///     "-343412345678910111213141516171819202122232425262728293031",
    /// ] {
    ///     let number: Number = serde_json::from_str(value).unwrap();
    ///     assert_eq!(number.as_str(), value);
    /// }
    /// ```
    #[cfg(feature = "arbitrary_precision")]
    #[cfg_attr(docsrs, doc(cfg(feature = "arbitrary_precision")))]
    pub fn as_str(&self) -> &str {
        &self.n
    }

    pub(crate) fn as_f32(&self) -> Option<f32> {
        #[cfg(not(feature = "arbitrary_precision"))]
        match self.n {
            N::PosInt(n) => Some(n as f32),
            N::NegInt(n) => Some(n as f32),
            N::PosInt128(n) => Some(n as f32),
            N::NegInt128(n) => Some(n as f32),
            N::Float(n) => Some(n as f32),
        }
        #[cfg(feature = "arbitrary_precision")]
        self.n.parse::<f32>().ok().filter(|float| float.is_finite())
    }

    pub(crate) fn from_f32(f: f32) -> Option<Number> {
        if f.is_finite() {
            let n = {
                #[cfg(not(feature = "arbitrary_precision"))]
                {
                    N::Float(f as f64)
                }
                #[cfg(feature = "arbitrary_precision")]
                {
                    ryu::Buffer::new().format_finite(f).to_owned()
                }
            };
            Some(Number { n })
        } else {
            None
        }
    }

    /// Returns true if this number is neither infinite nor NaN.
    pub fn from_u128(f: u128) -> Option<Number> {
        let n = {
            #[cfg(not(feature = "arbitrary_precision"))]
            {
                N::PosInt128(f)
            }
            #[cfg(feature = "arbitrary_precision")]
            {
                itoa::Buffer::new().format(f).to_owned()
            }
        };
        Some(Number { n })
    }

    /// Returns true if this number is neither infinite nor NaN.
    pub fn from_i128(f: i128) -> Option<Number> {
        let n = {
            #[cfg(not(feature = "arbitrary_precision"))]
            {
                N::NegInt128(f)
            }
            #[cfg(feature = "arbitrary_precision")]
            {
                itoa::Buffer::new().format(f).to_owned()
            }
        };
        Some(Number { n })
    }

    #[cfg(feature = "arbitrary_precision")]
    /// Not public API. Only tests use this.
    #[doc(hidden)]
    #[inline]
    pub fn from_string_unchecked(n: String) -> Self {
        Number { n }
    }
}

impl Display for Number {
    #[cfg(not(feature = "arbitrary_precision"))]
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self.n {
            N::PosInt(u) => formatter.write_str(itoa::Buffer::new().format(u)),
            N::NegInt(i) => formatter.write_str(itoa::Buffer::new().format(i)),
            N::Float(f) => formatter.write_str(ryu::Buffer::new().format_finite(f)),
            N::PosInt128(i) => formatter.write_str(itoa::Buffer::new().format(i)),
            N::NegInt128(i) => formatter.write_str(itoa::Buffer::new().format(i)),
        }
    }

    #[cfg(feature = "arbitrary_precision")]
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(&self.n, formatter)
    }
}

impl Debug for Number {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "Number({})", self)
    }
}

impl Serialize for Number {
    #[cfg(not(feature = "arbitrary_precision"))]
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self.n {
            N::PosInt(u) => serializer.serialize_u64(u),
            N::NegInt(i) => serializer.serialize_i64(i),
            N::Float(f) => serializer.serialize_f64(f),
            N::PosInt128(i) => serializer.serialize_u128(i),
            N::NegInt128(i) => serializer.serialize_i128(i),
        }
    }

    #[cfg(feature = "arbitrary_precision")]
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeStruct;

        let mut s = tri!(serializer.serialize_struct(TOKEN, 1));
        tri!(s.serialize_field(TOKEN, &self.n));
        s.end()
    }
}

impl<'de> Deserialize<'de> for Number {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Number, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct NumberVisitor;

        impl<'de> Visitor<'de> for NumberVisitor {
            type Value = Number;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a JSON number")
            }

            #[inline]
            fn visit_i64<E>(self, value: i64) -> Result<Number, E> {
                Ok(value.into())
            }

            #[inline]
            fn visit_u64<E>(self, value: u64) -> Result<Number, E> {
                Ok(value.into())
            }

            #[inline]
            fn visit_f64<E>(self, value: f64) -> Result<Number, E>
            where
                E: de::Error,
            {
                Number::from_f64(value).ok_or_else(|| de::Error::custom("not a JSON number"))
            }

            #[inline]
            fn visit_i128<E>(self, value: i128) -> Result<Number, E> {
                Ok(Number::from_i128(value).unwrap())
            }

            #[inline]
            fn visit_u128<E>(self, value: u128) -> Result<Number, E> {
                Ok(Number::from_u128(value).unwrap())
            }

            #[cfg(feature = "arbitrary_precision")]
            #[inline]
            fn visit_map<V>(self, mut visitor: V) -> Result<Number, V::Error>
            where
                V: de::MapAccess<'de>,
            {
                let value = tri!(visitor.next_key::<NumberKey>());
                if value.is_none() {
                    return Err(de::Error::invalid_type(Unexpected::Map, &self));
                }
                let v: NumberFromString = tri!(visitor.next_value());
                Ok(v.value)
            }
        }

        deserializer.deserialize_any(NumberVisitor)
    }
}

#[cfg(feature = "arbitrary_precision")]
struct NumberKey;

#[cfg(feature = "arbitrary_precision")]
impl<'de> de::Deserialize<'de> for NumberKey {
    fn deserialize<D>(deserializer: D) -> Result<NumberKey, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct FieldVisitor;

        impl<'de> de::Visitor<'de> for FieldVisitor {
            type Value = ();

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a valid number field")
            }

            fn visit_str<E>(self, s: &str) -> Result<(), E>
            where
                E: de::Error,
            {
                if s == TOKEN {
                    Ok(())
                } else {
                    Err(de::Error::custom("expected field with custom name"))
                }
            }
        }

        tri!(deserializer.deserialize_identifier(FieldVisitor));
        Ok(NumberKey)
    }
}

#[cfg(feature = "arbitrary_precision")]
pub struct NumberFromString {
    pub value: Number,
}

#[cfg(feature = "arbitrary_precision")]
impl<'de> de::Deserialize<'de> for NumberFromString {
    fn deserialize<D>(deserializer: D) -> Result<NumberFromString, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct Visitor;

        impl<'de> de::Visitor<'de> for Visitor {
            type Value = NumberFromString;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("string containing a number")
            }

            fn visit_str<E>(self, s: &str) -> Result<NumberFromString, E>
            where
                E: de::Error,
            {
                let n = tri!(s.parse().map_err(de::Error::custom));
                Ok(NumberFromString { value: n })
            }
        }

        deserializer.deserialize_str(Visitor)
    }
}

#[cfg(feature = "arbitrary_precision")]
fn invalid_number() -> Error {
    Error::syntax(ErrorCode::InvalidNumber, 0, 0)
}

macro_rules! deserialize_any {
    (@expand [$($num_string:tt)*]) => {
        #[cfg(not(feature = "arbitrary_precision"))]
        #[inline]
        fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: Visitor<'de>,
        {
            match self.n {
                N::PosInt(u) => visitor.visit_u64(u),
                N::NegInt(i) => visitor.visit_i64(i),
                N::Float(f) => visitor.visit_f64(f),
                N::PosInt128(i) => visitor.visit_u128(i),
                N::NegInt128(i) => visitor.visit_i128(i),
            }
        }

        #[cfg(feature = "arbitrary_precision")]
        #[inline]
        fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Error>
            where V: Visitor<'de>
        {
            if let Some(u) = self.as_u64() {
                return visitor.visit_u64(u);
            } else if let Some(i) = self.as_i64() {
                return visitor.visit_i64(i);
            } else if let Some(f) = self.as_f64() {
                if ryu::Buffer::new().format_finite(f) == self.n || f.to_string() == self.n {
                    return visitor.visit_f64(f);
                }
            }

            visitor.visit_map(NumberDeserializer {
                number: Some(self.$($num_string)*),
            })
        }
    };

    (owned) => {
        deserialize_any!(@expand [n]);
    };

    (ref) => {
        deserialize_any!(@expand [n.clone()]);
    };
}

macro_rules! deserialize_number {
    ($deserialize:ident => $visit:ident) => {
        #[cfg(not(feature = "arbitrary_precision"))]
        fn $deserialize<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: Visitor<'de>,
        {
            self.deserialize_any(visitor)
        }

        #[cfg(feature = "arbitrary_precision")]
        fn $deserialize<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: de::Visitor<'de>,
        {
            visitor.$visit(tri!(self.n.parse().map_err(|_| invalid_number())))
        }
    };
}

impl<'de> Deserializer<'de> for Number {
    type Error = Error;

    deserialize_any!(owned);

    deserialize_number!(deserialize_i8 => visit_i8);
    deserialize_number!(deserialize_i16 => visit_i16);
    deserialize_number!(deserialize_i32 => visit_i32);
    deserialize_number!(deserialize_i64 => visit_i64);
    deserialize_number!(deserialize_i128 => visit_i128);
    deserialize_number!(deserialize_u8 => visit_u8);
    deserialize_number!(deserialize_u16 => visit_u16);
    deserialize_number!(deserialize_u32 => visit_u32);
    deserialize_number!(deserialize_u64 => visit_u64);
    deserialize_number!(deserialize_u128 => visit_u128);
    deserialize_number!(deserialize_f32 => visit_f32);
    deserialize_number!(deserialize_f64 => visit_f64);

    forward_to_deserialize_any! {
        bool char str string bytes byte_buf option unit unit_struct
        newtype_struct seq tuple tuple_struct map struct enum identifier
        ignored_any
    }
}

impl<'de, 'a> Deserializer<'de> for &'a Number {
    type Error = Error;

    deserialize_any!(ref);

    deserialize_number!(deserialize_i8 => visit_i8);
    deserialize_number!(deserialize_i16 => visit_i16);
    deserialize_number!(deserialize_i32 => visit_i32);
    deserialize_number!(deserialize_i64 => visit_i64);
    deserialize_number!(deserialize_i128 => visit_i128);
    deserialize_number!(deserialize_u8 => visit_u8);
    deserialize_number!(deserialize_u16 => visit_u16);
    deserialize_number!(deserialize_u32 => visit_u32);
    deserialize_number!(deserialize_u64 => visit_u64);
    deserialize_number!(deserialize_u128 => visit_u128);
    deserialize_number!(deserialize_f32 => visit_f32);
    deserialize_number!(deserialize_f64 => visit_f64);

    forward_to_deserialize_any! {
        bool char str string bytes byte_buf option unit unit_struct
        newtype_struct seq tuple tuple_struct map struct enum identifier
        ignored_any
    }
}

#[cfg(feature = "arbitrary_precision")]
pub(crate) struct NumberDeserializer {
    pub number: Option<String>,
}

#[cfg(feature = "arbitrary_precision")]
impl<'de> MapAccess<'de> for NumberDeserializer {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Error>
    where
        K: de::DeserializeSeed<'de>,
    {
        if self.number.is_none() {
            return Ok(None);
        }
        seed.deserialize(NumberFieldDeserializer).map(Some)
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Error>
    where
        V: de::DeserializeSeed<'de>,
    {
        seed.deserialize(self.number.take().unwrap().into_deserializer())
    }
}

#[cfg(feature = "arbitrary_precision")]
struct NumberFieldDeserializer;

#[cfg(feature = "arbitrary_precision")]
impl<'de> Deserializer<'de> for NumberFieldDeserializer {
    type Error = Error;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Error>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_borrowed_str(TOKEN)
    }

    forward_to_deserialize_any! {
        bool u8 u16 u32 u64 u128 i8 i16 i32 i64 i128 f32 f64 char str string seq
        bytes byte_buf map struct option unit newtype_struct ignored_any
        unit_struct tuple_struct tuple enum identifier
    }
}

impl From<ParserNumber> for Number {
    fn from(value: ParserNumber) -> Self {
        let n = match value {
            ParserNumber::F64(f) => {
                #[cfg(not(feature = "arbitrary_precision"))]
                {
                    N::Float(f)
                }
                #[cfg(feature = "arbitrary_precision")]
                {
                    f.to_string()
                }
            }
            ParserNumber::U64(u) => {
                #[cfg(not(feature = "arbitrary_precision"))]
                {
                    N::PosInt(u)
                }
                #[cfg(feature = "arbitrary_precision")]
                {
                    u.to_string()
                }
            }
            ParserNumber::U128(u) => {
                #[cfg(not(feature = "arbitrary_precision"))]
                {
                    N::PosInt128(u)
                }
                #[cfg(feature = "arbitrary_precision")]
                {
                    u.to_string()
                }
            }
            ParserNumber::I64(i) => {
                #[cfg(not(feature = "arbitrary_precision"))]
                {
                    N::NegInt(i)
                }
                #[cfg(feature = "arbitrary_precision")]
                {
                    i.to_string()
                }
            }
            ParserNumber::I128(i) => {
                #[cfg(not(feature = "arbitrary_precision"))]
                {
                    N::NegInt128(i)
                }
                #[cfg(feature = "arbitrary_precision")]
                {
                    i.to_string()
                }
            }
            #[cfg(feature = "arbitrary_precision")]
            ParserNumber::String(s) => s,
        };
        Number { n }
    }
}

macro_rules! impl_from_unsigned {
    (
        $($ty:ty),*
    ) => {
        $(
            impl From<$ty> for Number {
                #[inline]
                fn from(u: $ty) -> Self {
                    let n = {
                        #[cfg(not(feature = "arbitrary_precision"))]
                        { N::PosInt(u as u64) }
                        #[cfg(feature = "arbitrary_precision")]
                        {
                            itoa::Buffer::new().format(u).to_owned()
                        }
                    };
                    Number { n }
                }
            }
        )*
    };
}

macro_rules! impl_from_signed {
    (
        $($ty:ty),*
    ) => {
        $(
            impl From<$ty> for Number {
                #[inline]
                fn from(i: $ty) -> Self {
                    let n = {
                        #[cfg(not(feature = "arbitrary_precision"))]
                        {
                            if i < 0 {
                                N::NegInt(i as i64)
                            } else {
                                N::PosInt(i as u64)
                            }
                        }
                        #[cfg(feature = "arbitrary_precision")]
                        {
                            itoa::Buffer::new().format(i).to_owned()
                        }
                    };
                    Number { n }
                }
            }
        )*
    };
}

impl_from_unsigned!(u8, u16, u32, u64, usize);
impl_from_signed!(i8, i16, i32, i64, isize);

impl From<i128> for Number {
    fn from(f: i128) -> Self {
        let n = {
            #[cfg(not(feature = "arbitrary_precision"))]
            {
                N::NegInt128(f)
            }
            #[cfg(feature = "arbitrary_precision")]
            {
                itoa::Buffer::new().format(f).to_owned()
            }
        };
        Number { n }
    }
}

impl From<u128> for Number {
    fn from(f: u128) -> Self {
        let n = {
            #[cfg(not(feature = "arbitrary_precision"))]
            {
                N::PosInt128(f)
            }
            #[cfg(feature = "arbitrary_precision")]
            {
                itoa::Buffer::new().format(f).to_owned()
            }
        };
        Number { n }
    }
}

impl Number {
    #[cfg(not(feature = "arbitrary_precision"))]
    #[cold]
    pub(crate) fn unexpected(&self) -> Unexpected {
        match self.n {
            N::PosInt(u) => Unexpected::Unsigned(u),
            N::NegInt(i) => Unexpected::Signed(i),
            N::Float(f) => Unexpected::Float(f),
            N::PosInt128(i) => Unexpected::from(ExtendedUnexpected::Unsigned(i)),
            N::NegInt128(i) => Unexpected::from(ExtendedUnexpected::Signed(i)),
        }
    }

    #[cfg(feature = "arbitrary_precision")]
    #[cold]
    pub(crate) fn unexpected(&self) -> Unexpected {
        Unexpected::Other("number")
    }
}

pub enum ExtendedUnexpected<'a> {
    External(Unexpected<'a>),
    Unsigned(u128),
    Signed(i128),
}

impl<'a> From<Unexpected<'a>> for ExtendedUnexpected<'a> {
    fn from(item: Unexpected<'a>) -> Self {
        ExtendedUnexpected::External(item)
    }
}

impl<'a> From<ExtendedUnexpected<'a>> for Unexpected<'a> {
    fn from(item: ExtendedUnexpected<'a>) -> Self {
        match item {
            ExtendedUnexpected::External(external) => external,
            _ => panic!("Trying to convert from a variant that is not External"),
        }
    }
}
