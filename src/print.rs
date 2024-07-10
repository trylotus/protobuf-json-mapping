use std::fmt;
use std::fmt::Write as fmt_Write;

use lotus_proto::lotus;
use lotus_proto::lotus::FormatType::FORMAT_TYPE_BASE64;
use lotus_proto::lotus::FormatType::FORMAT_TYPE_HEX;
use protobuf::descriptor::FieldOptions;
use protobuf::reflect::EnumDescriptor;
use protobuf::reflect::EnumValueDescriptor;
use protobuf::reflect::MessageRef;
use protobuf::reflect::ReflectFieldRef;
use protobuf::reflect::ReflectMapRef;
use protobuf::reflect::ReflectRepeatedRef;
use protobuf::reflect::ReflectValueRef;
use protobuf::reflect::RuntimeFieldType;
use protobuf::reflect::RuntimeType;
use protobuf::well_known_types::any::Any;
use protobuf::well_known_types::duration::Duration;
use protobuf::well_known_types::field_mask::FieldMask;
use protobuf::well_known_types::struct_::value;
use protobuf::well_known_types::struct_::ListValue;
use protobuf::well_known_types::struct_::NullValue;
use protobuf::well_known_types::struct_::Struct;
use protobuf::well_known_types::struct_::Value;
use protobuf::well_known_types::timestamp::Timestamp;
use protobuf::well_known_types::wrappers::BoolValue;
use protobuf::well_known_types::wrappers::BytesValue;
use protobuf::well_known_types::wrappers::DoubleValue;
use protobuf::well_known_types::wrappers::FloatValue;
use protobuf::well_known_types::wrappers::Int32Value;
use protobuf::well_known_types::wrappers::Int64Value;
use protobuf::well_known_types::wrappers::StringValue;
use protobuf::well_known_types::wrappers::UInt32Value;
use protobuf::well_known_types::wrappers::UInt64Value;
use protobuf::MessageDyn;
use protobuf::MessageField;

use crate::base64;
use crate::float;
use crate::rfc_3339::TmUtc;
use crate::well_known_wrapper::WellKnownWrapper;

#[derive(Debug, thiserror::Error)]
enum PrintErrorInner {
    #[error(transparent)]
    Fmt(fmt::Error),
    #[error("JSON printing of Any is not implemented")]
    AnyPrintingIsNotImplemented,
    #[error("Negative nanoseconds in timestamp")]
    TimestampNegativeNanos,
    #[error("Unknown struct value kind")]
    UnknownStructValueKind,
}

/// Print to JSON error.
#[derive(Debug, thiserror::Error)]
#[error(transparent)]
pub struct PrintError(PrintErrorInner);

impl From<fmt::Error> for PrintError {
    fn from(e: fmt::Error) -> Self {
        PrintError(PrintErrorInner::Fmt(e))
    }
}

pub type PrintResult<T> = Result<T, PrintError>;

struct Printer {
    buf: String,
    print_options: PrintOptions,
}

trait PrintableToJson {
    fn print_to_json(
        &self,
        w: &mut Printer,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()>;
}

trait JsonFloat: fmt::Display + fmt::Debug + PrintableToJson {
    fn is_nan(&self) -> bool;
    fn is_pos_infinity(&self) -> bool;
    fn is_neg_infinity(&self) -> bool;

    fn print_to_json_impl(&self, w: &mut String) -> PrintResult<()> {
        Ok(if self.is_nan() {
            write!(w, "\"{}\"", float::PROTOBUF_JSON_NAN)?
        } else if self.is_pos_infinity() {
            write!(w, "\"{}\"", float::PROTOBUF_JSON_INF)?
        } else if self.is_neg_infinity() {
            write!(w, "\"{}\"", float::PROTOBUF_JSON_MINUS_INF)?
        } else {
            write!(w, "{:?}", self)?
        })
    }
}

impl JsonFloat for f32 {
    fn is_nan(&self) -> bool {
        f32::is_nan(*self)
    }

    fn is_pos_infinity(&self) -> bool {
        f32::is_infinite(*self) && self > &0.0
    }

    fn is_neg_infinity(&self) -> bool {
        f32::is_infinite(*self) && self < &0.0
    }
}

impl PrintableToJson for f32 {
    fn print_to_json(&self, w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        Ok(self.print_to_json_impl(&mut w.buf)?)
    }
}

impl JsonFloat for f64 {
    fn is_nan(&self) -> bool {
        f64::is_nan(*self)
    }

    fn is_pos_infinity(&self) -> bool {
        f64::is_infinite(*self) && self > &0.0
    }

    fn is_neg_infinity(&self) -> bool {
        f64::is_infinite(*self) && self < &0.0
    }
}

impl PrintableToJson for f64 {
    fn print_to_json(&self, w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        self.print_to_json_impl(&mut w.buf)
    }
}

impl PrintableToJson for u64 {
    fn print_to_json(&self, w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        // 64-bit integers are quoted by default
        Ok(write!(w.buf, "\"{}\"", self)?)
    }
}

impl PrintableToJson for i64 {
    fn print_to_json(&self, w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        // 64-bit integers are quoted by default
        Ok(write!(w.buf, "\"{}\"", self)?)
    }
}

impl PrintableToJson for u32 {
    fn print_to_json(&self, w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        Ok(write!(w.buf, "{}", self)?)
    }
}

impl PrintableToJson for i32 {
    fn print_to_json(&self, w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        Ok(write!(w.buf, "{}", self)?)
    }
}

impl PrintableToJson for bool {
    fn print_to_json(&self, w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        Ok(write!(w.buf, "{}", self)?)
    }
}

impl PrintableToJson for str {
    fn print_to_json(&self, w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        write!(w.buf, "\"")?;
        for c in self.chars() {
            match c {
                '"' => write!(w.buf, "\\\""),
                '\\' => write!(w.buf, "\\\\"),
                '\n' => write!(w.buf, "\\n"),
                '\r' => write!(w.buf, "\\r"),
                '\t' => write!(w.buf, "\\t"),
                c if c.is_control() => write!(w.buf, "\\u{:04x}", c as u32),
                c => write!(w.buf, "{}", c),
            }?;
        }
        write!(w.buf, "\"")?;
        Ok(())
    }
}

impl PrintableToJson for String {
    fn print_to_json(
        &self,
        w: &mut Printer,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        self.as_str().print_to_json(w, options)
    }
}

impl PrintableToJson for [u8] {
    fn print_to_json(
        &self,
        w: &mut Printer,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        let format = lotus::exts::bytes
            .get(options)
            .unwrap_or_default()
            .format
            .enum_value_or_default();

        let encoded = match format {
            FORMAT_TYPE_BASE64 => base64::encode(self),
            FORMAT_TYPE_HEX => format!("0x{}", hex::encode(self)),
        };

        encoded.print_to_json(w, options)
    }
}

impl PrintableToJson for Vec<u8> {
    fn print_to_json(
        &self,
        w: &mut Printer,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        self.as_slice().print_to_json(w, options)
    }
}

impl<'a> PrintableToJson for ReflectValueRef<'a> {
    fn print_to_json(
        &self,
        w: &mut Printer,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        match self {
            ReflectValueRef::U32(v) => w.print_printable(v, options),
            ReflectValueRef::U64(v) => w.print_printable(v, options),
            ReflectValueRef::I32(v) => w.print_printable(v, options),
            ReflectValueRef::I64(v) => w.print_printable(v, options),
            ReflectValueRef::F32(v) => w.print_printable(v, options),
            ReflectValueRef::F64(v) => w.print_printable(v, options),
            ReflectValueRef::Bool(v) => w.print_printable(v, options),
            ReflectValueRef::String(v) => w.print_printable::<str>(v, options),
            ReflectValueRef::Bytes(v) => w.print_printable::<[u8]>(v, options),
            ReflectValueRef::Enum(d, v) => w.print_enum(d, *v),
            ReflectValueRef::Message(v) => w.print_message(v),
        }
    }
}

impl PrintableToJson for Duration {
    fn print_to_json(&self, w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        let sign = if self.seconds >= 0 { "" } else { "-" };
        Ok(write!(
            w.buf,
            "\"{}{}.{:09}s\"",
            sign,
            self.seconds.abs(),
            self.nanos.abs()
        )?)
    }
}

impl PrintableToJson for Timestamp {
    fn print_to_json(
        &self,
        w: &mut Printer,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        if self.nanos < 0 {
            return Err(PrintError(PrintErrorInner::TimestampNegativeNanos));
        }
        let tm_utc = TmUtc::from_protobuf_timestamp(self.seconds, self.nanos as u32);
        w.print_printable(&tm_utc.to_string(), options)
    }
}

impl PrintableToJson for FieldMask {
    fn print_to_json(
        &self,
        w: &mut Printer,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        w.print_printable(&self.paths.join(","), options)
    }
}

impl PrintableToJson for Any {
    fn print_to_json(&self, _w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        Err(PrintError(PrintErrorInner::AnyPrintingIsNotImplemented))
    }
}

impl PrintableToJson for Value {
    fn print_to_json(
        &self,
        w: &mut Printer,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        match self.kind {
            // None should not be possible here, but it's better to print null than crash
            None => w.print_json_null(),
            Some(value::Kind::NullValue(null_value)) => {
                match null_value.enum_value() {
                    Ok(value) => w.print_wk_null_value(&value),
                    Err(n) => {
                        // Practically not possible, but it is safer this way.
                        w.print_printable(&n, options)
                    }
                }
            }
            Some(value::Kind::BoolValue(b)) => w.print_printable(&b, options),
            Some(value::Kind::NumberValue(n)) => w.print_printable(&n, options),
            Some(value::Kind::StringValue(ref s)) => w.print_printable::<String>(&s, options),
            Some(value::Kind::StructValue(ref s)) => w.print_printable(&s, options),
            Some(value::Kind::ListValue(ref l)) => w.print_printable(&l, options),
            Some(_) => Err(PrintError(PrintErrorInner::UnknownStructValueKind)),
        }
    }
}

impl PrintableToJson for ListValue {
    fn print_to_json(
        &self,
        w: &mut Printer,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        w.print_list(&self.values, options)
    }
}

impl PrintableToJson for Struct {
    fn print_to_json(&self, w: &mut Printer, _: &MessageField<FieldOptions>) -> PrintResult<()> {
        w.print_object(&self.fields)
    }
}

impl<'a, P: PrintableToJson> PrintableToJson for &'a P {
    fn print_to_json(
        &self,
        w: &mut Printer,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        (*self).print_to_json(w, options)
    }
}

trait ObjectKey {
    fn print_object_key(&self, w: &mut Printer) -> PrintResult<()>;
}

impl<'a> ObjectKey for ReflectValueRef<'a> {
    fn print_object_key(&self, w: &mut Printer) -> PrintResult<()> {
        match self {
            ReflectValueRef::String(v) => {
                return w.print_printable::<str>(v, &MessageField::none())
            }
            ReflectValueRef::Bytes(v) => {
                return w.print_printable::<[u8]>(v, &MessageField::none())
            }
            // do not quote, because printable is quoted
            ReflectValueRef::U64(v) => return w.print_printable(v, &MessageField::none()),
            ReflectValueRef::I64(v) => return w.print_printable(v, &MessageField::none()),
            ReflectValueRef::Enum(d, v) if !w.print_options.enum_values_int => {
                return w.print_enum(d, *v)
            }
            _ => {}
        }

        write!(w.buf, "\"")?;

        match self {
            ReflectValueRef::U32(v) => w.print_printable(v, &MessageField::none()),
            ReflectValueRef::I32(v) => w.print_printable(v, &MessageField::none()),
            ReflectValueRef::Bool(v) => w.print_printable(v, &MessageField::none()),
            ReflectValueRef::Enum(d, v) if w.print_options.enum_values_int => w.print_enum(d, *v),
            ReflectValueRef::Enum(..)
            | ReflectValueRef::U64(_)
            | ReflectValueRef::I64(_)
            | ReflectValueRef::String(_)
            | ReflectValueRef::Bytes(_) => unreachable!(),
            ReflectValueRef::F32(_) | ReflectValueRef::F64(_) | ReflectValueRef::Message(_) => {
                panic!("cannot be object key")
            }
        }?;

        write!(w.buf, "\"")?;

        Ok(())
    }
}

impl ObjectKey for String {
    fn print_object_key(&self, w: &mut Printer) -> PrintResult<()> {
        w.print_printable(self, &MessageField::none())
    }
}

impl<'a, O: ObjectKey> ObjectKey for &'a O {
    fn print_object_key(&self, w: &mut Printer) -> PrintResult<()> {
        (*self).print_object_key(w)
    }
}

impl Printer {
    fn print_comma_but_first(&mut self, first: &mut bool) -> fmt::Result {
        if *first {
            *first = false;
            Ok(())
        } else {
            write!(self.buf, ", ")
        }
    }

    fn print_json_null(&mut self) -> PrintResult<()> {
        Ok(write!(self.buf, "null")?)
    }

    fn print_printable<F: PrintableToJson + ?Sized>(
        &mut self,
        f: &F,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        f.print_to_json(self, options)
    }

    fn print_list<I>(&mut self, items: I, options: &MessageField<FieldOptions>) -> PrintResult<()>
    where
        I: IntoIterator,
        I::Item: PrintableToJson,
    {
        write!(self.buf, "[")?;
        for (i, item) in items.into_iter().enumerate() {
            if i != 0 {
                write!(self.buf, ", ")?;
            }
            self.print_printable(&item, options)?;
        }
        write!(self.buf, "]")?;
        Ok(())
    }

    fn print_repeated(
        &mut self,
        repeated: &ReflectRepeatedRef,
        options: &MessageField<FieldOptions>,
    ) -> PrintResult<()> {
        self.print_list(repeated, options)
    }

    fn print_object<I, K, V>(&mut self, items: I) -> PrintResult<()>
    where
        I: IntoIterator<Item = (K, V)>,
        K: ObjectKey,
        V: PrintableToJson,
    {
        write!(self.buf, "{{")?;
        for (i, (k, v)) in items.into_iter().enumerate() {
            if i != 0 {
                write!(self.buf, ", ")?;
            }
            k.print_object_key(self)?;
            write!(self.buf, ": ")?;
            self.print_printable(&v, &MessageField::none())?;
        }
        write!(self.buf, "}}")?;
        Ok(())
    }

    fn print_map(&mut self, map: &ReflectMapRef) -> PrintResult<()> {
        self.print_object(map.into_iter())
    }

    fn print_enum_known(&mut self, value: &EnumValueDescriptor) -> PrintResult<()> {
        if let Some(null_value) = value.cast() {
            self.print_wk_null_value(&null_value)
        } else {
            if self.print_options.enum_values_int {
                self.print_printable(&value.value(), &MessageField::none())
            } else {
                Ok(write!(self.buf, "\"{}\"", value.name())?)
            }
        }
    }

    fn print_enum(&mut self, descriptor: &EnumDescriptor, v: i32) -> PrintResult<()> {
        if self.print_options.enum_values_int {
            self.print_printable(&v, &MessageField::none())
        } else {
            match descriptor.value_by_number(v) {
                Some(value) => self.print_enum_known(&value),
                None => self.print_printable(&v, &MessageField::none()),
            }
        }
    }

    fn print_message(&mut self, message: &MessageRef) -> PrintResult<()> {
        if let Some(duration) = message.downcast_ref::<Duration>() {
            self.print_printable(duration, &MessageField::none())
        } else if let Some(timestamp) = message.downcast_ref::<Timestamp>() {
            self.print_printable(timestamp, &MessageField::none())
        } else if let Some(field_mask) = message.downcast_ref::<FieldMask>() {
            self.print_printable(field_mask, &MessageField::none())
        } else if let Some(any) = message.downcast_ref::<Any>() {
            self.print_printable(any, &MessageField::none())
        } else if let Some(value) = message.downcast_ref::<Value>() {
            self.print_printable(value, &MessageField::none())
        } else if let Some(value) = message.downcast_ref::<DoubleValue>() {
            self.print_wrapper(value)
        } else if let Some(value) = message.downcast_ref::<FloatValue>() {
            self.print_wrapper(value)
        } else if let Some(value) = message.downcast_ref::<Int64Value>() {
            self.print_wrapper(value)
        } else if let Some(value) = message.downcast_ref::<UInt64Value>() {
            self.print_wrapper(value)
        } else if let Some(value) = message.downcast_ref::<Int32Value>() {
            self.print_wrapper(value)
        } else if let Some(value) = message.downcast_ref::<UInt32Value>() {
            self.print_wrapper(value)
        } else if let Some(value) = message.downcast_ref::<BoolValue>() {
            self.print_wrapper(value)
        } else if let Some(value) = message.downcast_ref::<StringValue>() {
            self.print_wrapper(value)
        } else if let Some(value) = message.downcast_ref::<BytesValue>() {
            self.print_wrapper(value)
        } else if let Some(value) = message.downcast_ref::<ListValue>() {
            self.print_printable(value, &MessageField::none())
        } else if let Some(value) = message.downcast_ref::<Struct>() {
            self.print_printable(value, &MessageField::none())
        } else {
            self.print_regular_message(message)
        }
    }

    fn print_regular_message(&mut self, message: &MessageRef) -> Result<(), PrintError> {
        let descriptor = message.descriptor_dyn();

        write!(self.buf, "{{")?;
        let mut first = true;
        for field in descriptor.fields() {
            let json_field_name = if self.print_options.proto_field_name {
                field.name()
            } else {
                field.json_name()
            };

            let field_type = field.runtime_field_type();

            match field.get_reflect(&**message) {
                ReflectFieldRef::Optional(v) => match v.value() {
                    None => {
                        if self.print_options.always_output_default_values {
                            let is_message = match field_type {
                                RuntimeFieldType::Singular(s) => match s {
                                    RuntimeType::Message(_) => true,
                                    _ => false,
                                },
                                _ => unreachable!(),
                            };

                            let is_oneof = field.proto().has_oneof_index();

                            if !is_message && !is_oneof {
                                let v = field.get_singular_field_or_default(&**message);
                                self.print_comma_but_first(&mut first)?;
                                write!(self.buf, "\"{}\": ", json_field_name)?;
                                self.print_printable(&v, &field.proto().options)?;
                            }
                        }
                    }
                    Some(v) => {
                        self.print_comma_but_first(&mut first)?;
                        write!(self.buf, "\"{}\": ", json_field_name)?;
                        self.print_printable(&v, &field.proto().options)?;
                    }
                },
                ReflectFieldRef::Repeated(v) => {
                    if !v.is_empty() || self.print_options.always_output_default_values {
                        self.print_comma_but_first(&mut first)?;
                        write!(self.buf, "\"{}\": ", json_field_name)?;
                        self.print_repeated(&v, &field.proto().options)?;
                    }
                }
                ReflectFieldRef::Map(v) => {
                    if !v.is_empty() || self.print_options.always_output_default_values {
                        self.print_comma_but_first(&mut first)?;
                        write!(self.buf, "\"{}\": ", json_field_name)?;
                        self.print_map(&v)?;
                    }
                }
            }
        }
        write!(self.buf, "}}")?;
        Ok(())
    }

    fn print_wk_null_value(&mut self, _null_value: &NullValue) -> PrintResult<()> {
        self.print_json_null()
    }

    fn print_wrapper<W>(&mut self, value: &W) -> PrintResult<()>
    where
        W: WellKnownWrapper,
        W::Underlying: PrintableToJson,
    {
        self.print_printable(value.get_ref(), &MessageField::none())
    }
}

/// Options for printing JSON to string
///
/// # Examples
///
/// ```
/// let print_options = protobuf_json_mapping::PrintOptions {
///     enum_values_int: true,
///     ..Default::default()
/// };
/// ```
#[derive(Default, Debug, Clone)]
pub struct PrintOptions {
    /// Use ints instead of strings for enums.
    ///
    /// Note both string or int can be parsed.
    pub enum_values_int: bool,
    /// Use protobuf field names instead of `lowerCamelCase` which is used by default.
    /// Note both names are supported when JSON is parsed.
    pub proto_field_name: bool,
    /// Output field default values.
    pub always_output_default_values: bool,
    /// Prevent initializing `PrintOptions` enumerating all field.
    pub _future_options: (),
}

/// Serialize message to JSON according to protobuf specification.
pub fn print_to_string_with_options(
    message: &dyn MessageDyn,
    print_options: &PrintOptions,
) -> PrintResult<String> {
    let mut printer = Printer {
        buf: String::new(),
        print_options: print_options.clone(),
    };
    printer.print_message(&MessageRef::from(message))?;
    Ok(printer.buf)
}

/// Serialize message to JSON according to protobuf specification.
pub fn print_to_string(message: &dyn MessageDyn) -> PrintResult<String> {
    print_to_string_with_options(message, &PrintOptions::default())
}

#[test]
fn test_print_to_string() {
    use crate::test;

    let mut bar = test::foo::Bar::new();
    bar.hex = vec![
        hex::decode("48656c6c6f20776f726c6421").unwrap(),
        hex::decode("48656c6c6f20776f726c6421").unwrap(),
    ];
    bar.base64 = vec![
        base64::decode("SGVsbG8gd29ybGQh").unwrap(),
        base64::decode("SGVsbG8gd29ybGQh").unwrap(),
    ];

    let mut foo = test::foo::Foo::new();
    foo.hex = hex::decode("48656c6c6f20776f726c6421").unwrap();
    foo.base64 = base64::decode("SGVsbG8gd29ybGQh").unwrap();
    foo.bar = MessageField::some(bar);

    let txt = print_to_string(&foo).unwrap();

    assert_eq!(txt, "{\"hex\": \"0x48656c6c6f20776f726c6421\", \"base64\": \"SGVsbG8gd29ybGQh\", \"bar\": {\"hex\": [\"0x48656c6c6f20776f726c6421\", \"0x48656c6c6f20776f726c6421\"], \"base64\": [\"SGVsbG8gd29ybGQh\", \"SGVsbG8gd29ybGQh\"]}}")
}
