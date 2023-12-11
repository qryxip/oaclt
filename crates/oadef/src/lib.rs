use std::{
    convert::Infallible,
    ffi::{c_int, c_uint, c_void},
    fmt::{self, Debug},
    mem::ManuallyDrop,
    slice,
};

use derive_more::Into;
use duplicate::duplicate_item;
use thiserror::Error;
use windows::{
    core::{BSTR, GUID, PCWSTR},
    Win32::{
        Foundation::VARIANT_BOOL,
        System::{
            Com::{
                CLSIDFromProgID, CoCreateInstance, IDispatch, CLSCTX_ALL, DISPATCH_METHOD,
                DISPATCH_PROPERTYGET, DISPATCH_PROPERTYPUT, DISPPARAMS, SAFEARRAY,
            },
            Ole::{SafeArrayCreateVector, SafeArrayPutElement},
            Variant::{
                VARENUM, VARIANT, VARIANT_0_0_0, VT_ARRAY, VT_BOOL, VT_BSTR, VT_DISPATCH, VT_EMPTY,
                VT_I2, VT_I4, VT_I8, VT_INT, VT_R4, VT_R8, VT_SAFEARRAY, VT_UI2, VT_UI4, VT_UI8,
                VT_UINT, VT_VARIANT,
            },
        },
    },
};

pub use oadef_macros::{new, TryFrom_Out};

pub fn idispatch_from_prog_id(lpszprogid: PCWSTR) -> windows::core::Result<IDispatch> {
    let clsid = unsafe {
        // SAFETY: this function itself is safe?
        CLSIDFromProgID(lpszprogid)?
    };
    unsafe {
        // SAFETY: according to com-rs, this function itself is safe?
        CoCreateInstance(&clsid, None, CLSCTX_ALL)
    }
}

pub fn invoke<T>(disp: &IDispatch, name: &PCWSTR, op: Op) -> crate::Result<T>
where
    T: TryFrom<Out>,
    T::Error: Into<crate::Error>,
{
    let rgdispid = unsafe {
        // SAFETY: the arguments are `&_` and `&mut`, so this is safe?
        let mut rgdispid = 0;
        disp.GetIDsOfNames(&GUID::zeroed(), name, 1, LOCALE_USER_DEFAULT, &mut rgdispid)?;
        rgdispid
    };

    let wflags = match op {
        Op::PropertyGet => DISPATCH_PROPERTYGET,
        Op::PropertyPut(_) => DISPATCH_PROPERTYPUT,
        Op::Method(_) => DISPATCH_METHOD,
    };

    let mut dispparams = match op {
        Op::PropertyGet => vec![],
        Op::PropertyPut(param) => vec![param.try_into()?],
        Op::Method(params) => params
            .into_iter()
            .rev()
            .map(TryInto::try_into)
            .collect::<std::result::Result<Vec<_>, _>>()?,
    };
    let dispparams = &DISPPARAMS {
        cArgs: dispparams.len() as _,
        rgvarg: dispparams.as_mut_ptr(),
        ..Default::default()
    };

    let mut result = Default::default();
    let mut excepinfo = Default::default();
    let mut argerr = 0;

    let ok_or_err = unsafe {
        // SAFETY: The arguments are valid, so this is safe?
        disp.Invoke(
            rgdispid,
            &GUID::zeroed(),
            LOCALE_USER_DEFAULT,
            wflags,
            dispparams,
            Some(&mut result),
            Some(&mut excepinfo),
            Some(&mut argerr),
        )
    };

    if ok_or_err.is_err() {
        // FIXME
        dbg!(excepinfo);
        dbg!(argerr);
    }

    ok_or_err?;

    return unsafe {
        // SAFETY: `Invoke` should return a valid `VARIANT`.
        Out::from_win32(result)?
    }
    .try_into()
    .map_err(Into::into);

    const LOCALE_USER_DEFAULT: u32 = 0x400;
}

pub enum Op {
    PropertyGet,
    PropertyPut(Arg),
    Method(Vec<Arg>),
}

pub enum Arg {
    Bool(AtMost1D<VARIANT_BOOL>),
    Ui2(AtMost1D<u16>),
    Ui4(AtMost1D<u32>),
    Ui8(AtMost1D<u64>),
    Uint(AtMost1D<c_uint>),
    I2(AtMost1D<i16>),
    I4(AtMost1D<i32>),
    I8(AtMost1D<i64>),
    Int(AtMost1D<c_int>),
    R4(AtMost1D<f32>),
    R8(AtMost1D<f64>),
    Bstr(AtMost1D<BSTR>),
    IDispatch(AtMost1D<IDispatch>),
    DynArray(Vec<InputDynElement>),
}

impl TryFrom<Arg> for VARIANT {
    type Error = windows::core::Error;

    fn try_from(arg: Arg) -> windows::core::Result<Self> {
        #![allow(clippy::explicit_auto_deref)]

        return match arg {
            Arg::Bool(AtMost1D::D0(p)) => Ok(unsafe { d0(p) }),
            Arg::Bool(AtMost1D::D1(ps)) => unsafe { d1(&ps) },
            Arg::Ui2(AtMost1D::D0(n)) => Ok(unsafe { d0(n) }),
            Arg::Ui2(AtMost1D::D1(ns)) => unsafe { d1(&ns) },
            Arg::Ui4(AtMost1D::D0(n)) => Ok(unsafe { d0(n) }),
            Arg::Ui4(AtMost1D::D1(ns)) => unsafe { d1(&ns) },
            Arg::Ui8(AtMost1D::D0(n)) => Ok(unsafe { d0(n) }),
            Arg::Ui8(AtMost1D::D1(ns)) => unsafe { d1(&ns) },
            Arg::Uint(AtMost1D::D0(n)) => Ok(unsafe { d0(n) }),
            Arg::Uint(AtMost1D::D1(ns)) => unsafe { d1(&ns) },
            Arg::I2(AtMost1D::D0(i)) => Ok(unsafe { d0(i) }),
            Arg::I2(AtMost1D::D1(is)) => unsafe { d1(&is) },
            Arg::I4(AtMost1D::D0(i)) => Ok(unsafe { d0(i) }),
            Arg::I4(AtMost1D::D1(is)) => unsafe { d1(&is) },
            Arg::I8(AtMost1D::D0(i)) => Ok(unsafe { d0(i) }),
            Arg::I8(AtMost1D::D1(is)) => unsafe { d1(&is) },
            Arg::Int(AtMost1D::D0(i)) => Ok(unsafe { d0(i) }),
            Arg::Int(AtMost1D::D1(is)) => unsafe { d1(&is) },
            Arg::R4(AtMost1D::D0(v)) => Ok(unsafe { d0(v) }),
            Arg::R4(AtMost1D::D1(vs)) => unsafe { d1(&vs) },
            Arg::R8(AtMost1D::D0(v)) => Ok(unsafe { d0(v) }),
            Arg::R8(AtMost1D::D1(vs)) => unsafe { d1(&vs) },
            Arg::Bstr(AtMost1D::D0(s)) => Ok(unsafe { d0(s) }),
            Arg::Bstr(AtMost1D::D1(ss)) => unsafe { d1(&ss) },
            Arg::IDispatch(AtMost1D::D0(x)) => Ok(unsafe { d0(x) }),
            Arg::IDispatch(AtMost1D::D1(xs)) => unsafe { d1(&xs) },
            Arg::DynArray(xs) => dyn_array(xs),
        };

        unsafe fn d0<T: Element>(x: T) -> VARIANT {
            let mut v = VARIANT::default();
            (*v.Anonymous.Anonymous).vt = T::VT;
            x.set(&mut (*v.Anonymous.Anonymous).Anonymous);
            v
        }

        unsafe fn d1<T: Element>(xs: &[T]) -> windows::core::Result<VARIANT> {
            let array = SafeArrayCreateVector(T::VT, 0, xs.len() as _);
            if array.is_null() {
                todo!();
            }
            for (i, x) in xs.iter().enumerate() {
                let indices = [i as _];
                SafeArrayPutElement(array, indices.as_ptr(), x as *const T as *const c_void)?;
            }

            let mut v = VARIANT::default();
            (*v.Anonymous.Anonymous).vt = VT_SAFEARRAY;
            (*v.Anonymous.Anonymous).Anonymous.parray = array;
            Ok(v)
        }

        fn dyn_array(xs: Vec<InputDynElement>) -> windows::core::Result<VARIANT> {
            // SAFETY: ?
            unsafe {
                let arr = SafeArrayCreateVector(VT_VARIANT, 0, xs.len() as _);
                if arr.is_null() {
                    todo!();
                }
                for (i, x) in xs.into_iter().enumerate() {
                    match x {
                        InputDynElement::Bool(x) => put_variant(arr, i, x),
                        InputDynElement::Ui2(x) => put_variant(arr, i, x),
                        InputDynElement::Ui4(x) => put_variant(arr, i, x),
                        InputDynElement::Ui8(x) => put_variant(arr, i, x),
                        InputDynElement::Uint(x) => put_variant(arr, i, x),
                        InputDynElement::I2(x) => put_variant(arr, i, x),
                        InputDynElement::I4(x) => put_variant(arr, i, x),
                        InputDynElement::I8(x) => put_variant(arr, i, x),
                        InputDynElement::Int(x) => put_variant(arr, i, x),
                        InputDynElement::R4(x) => put_variant(arr, i, x),
                        InputDynElement::R8(x) => put_variant(arr, i, x),
                        InputDynElement::Bstr(x) => put_variant(arr, i, x),
                        InputDynElement::IDispatch(x) => put_variant(arr, i, x),
                        InputDynElement::Array(xs) => {
                            let indices = [i as _];
                            let elem = &dyn_array(xs)?;
                            SafeArrayPutElement(
                                arr,
                                indices.as_ptr(),
                                elem as *const VARIANT as *const c_void,
                            )
                        }
                    }?;
                }

                let mut v = VARIANT::default();
                (*v.Anonymous.Anonymous).vt = VARENUM(VT_ARRAY.0 | VT_VARIANT.0);
                (*v.Anonymous.Anonymous).Anonymous.parray = arr;
                Ok(v)
            }
        }

        unsafe fn put_variant(
            arr: *const SAFEARRAY,
            idx: usize,
            elem: impl Element,
        ) -> windows::core::Result<()> {
            let indices = [idx as _];
            let elem = &d0(elem);
            SafeArrayPutElement(
                arr,
                indices.as_ptr(),
                elem as *const VARIANT as *const c_void,
            )
        }

        trait Element {
            const VT: VARENUM;
            fn set(self, v: &mut VARIANT_0_0_0);
        }

        impl Element for VARIANT_BOOL {
            const VT: VARENUM = VT_BOOL;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.boolVal = self;
            }
        }

        impl Element for u16 {
            const VT: VARENUM = VT_UI2;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.uiVal = self;
            }
        }

        impl Element for u32 {
            const VT: VARENUM = VT_UI4;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.ulVal = self;
            }
        }

        impl Element for u64 {
            const VT: VARENUM = VT_UI8;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.ullVal = self;
            }
        }

        impl Element for i16 {
            const VT: VARENUM = VT_I2;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.iVal = self;
            }
        }

        impl Element for i32 {
            const VT: VARENUM = VT_I4;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.lVal = self;
            }
        }

        impl Element for i64 {
            const VT: VARENUM = VT_I8;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.llVal = self;
            }
        }

        impl Element for f32 {
            const VT: VARENUM = VT_R4;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.fltVal = self;
            }
        }

        impl Element for f64 {
            const VT: VARENUM = VT_R8;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.dblVal = self;
            }
        }

        impl Element for BSTR {
            const VT: VARENUM = VT_BSTR;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.bstrVal = ManuallyDrop::new(self);
            }
        }

        impl Element for IDispatch {
            const VT: VARENUM = VT_DISPATCH;

            fn set(self, v: &mut VARIANT_0_0_0) {
                v.pdispVal = ManuallyDrop::new(Some(self));
            }
        }
    }
}

macro_rules! impl_arg_from_prim {
    ($($variant:path : $ty:ty;)*) => {
        $(
            impl From<$ty> for Arg {
                fn from(p: $ty) -> Self {
                    $variant(AtMost1D::D0(p.into()))
                }
            }

            impl From<&'_ [$ty]> for Arg {
                fn from(ps: &[$ty]) -> Self {
                    $variant(AtMost1D::D1(ps.iter().copied().map(Into::into).collect()))
                }
            }

            impl From<Vec<$ty>> for Arg {
                fn from(ps: Vec<$ty>) -> Self {
                    $variant(AtMost1D::D1(ps.into_iter().map(Into::into).collect()))
                }
            }
        )*
    };
}

impl_arg_from_prim! {
    Self::Bool: bool;
    Self::Ui2: u16;
    Self::Ui4: u32;
    Self::Ui8: u64;
    Self::Uint: CUint;
    Self::I2: i16;
    Self::I4: i32;
    Self::I8: i64;
    Self::Int: CInt;
    Self::R4: f32;
    Self::R8: f64;
}

impl From<&'_ str> for Arg {
    fn from(s: &'_ str) -> Self {
        Self::Bstr(AtMost1D::D0(s.into()))
    }
}

impl From<&'_ String> for Arg {
    fn from(s: &'_ String) -> Self {
        Self::Bstr(AtMost1D::D0(s.into()))
    }
}

impl From<&'_ [&'_ str]> for Arg {
    fn from(ss: &'_ [&'_ str]) -> Self {
        Self::Bstr(AtMost1D::D1(ss.iter().copied().map(Into::into).collect()))
    }
}

impl From<&'_ [String]> for Arg {
    fn from(ss: &'_ [String]) -> Self {
        Self::Bstr(AtMost1D::D1(ss.iter().map(Into::into).collect()))
    }
}

impl From<IDispatch> for Arg {
    fn from(disp: IDispatch) -> Self {
        Self::IDispatch(AtMost1D::D0(disp))
    }
}

impl From<Vec<IDispatch>> for Arg {
    fn from(disps: Vec<IDispatch>) -> Self {
        Self::IDispatch(AtMost1D::D1(disps))
    }
}

impl From<Vec<InputDynElement>> for Arg {
    fn from(args: Vec<InputDynElement>) -> Self {
        Self::DynArray(args)
    }
}

pub enum InputDynElement {
    Bool(VARIANT_BOOL),
    Ui2(u16),
    Ui4(u32),
    Ui8(u64),
    Uint(c_uint),
    I2(i16),
    I4(i32),
    I8(i64),
    Int(c_int),
    R4(f32),
    R8(f64),
    Bstr(BSTR),
    IDispatch(IDispatch),
    Array(Vec<Self>),
}

#[duplicate_item(
    T Variant;
    [ bool ] [ Bool ];
    [ u16 ] [ Ui2 ];
    [ u32 ] [ Ui4 ];
    [ u64 ] [ Ui8 ];
    [ CUint ] [ Uint ];
    [ i16 ] [ I2 ];
    [ i32 ] [ I4 ];
    [ i64 ] [ I8 ];
    [ CInt ] [ Int ];
    [ f32 ] [ R4 ];
    [ f64 ] [ R8 ];
    [ BSTR ] [ Bstr ];
    [ &'_ str ] [ Bstr ];
    [ String ] [ Bstr ];
    [ IDispatch ] [ IDispatch ];
    [ Vec<Self> ] [ Array ];
)]
impl From<T> for InputDynElement {
    fn from(x: T) -> Self {
        #[allow(clippy::useless_conversion)]
        Self::Variant(x.into())
    }
}

#[derive(Clone, Copy, Into)]
pub struct CUint(pub c_uint);

#[derive(Clone, Copy, Into)]
pub struct CInt(pub c_int);

#[derive(Debug)]
pub enum Out {
    Empty,
    Bool(AtMost1D<bool>),
    Ui2(AtMost1D<u16>),
    Ui4(AtMost1D<u32>),
    Ui8(AtMost1D<u64>),
    Uint(AtMost1D<c_uint>),
    I2(AtMost1D<i16>),
    I4(AtMost1D<i32>),
    I8(AtMost1D<i64>),
    Int(AtMost1D<c_int>),
    R4(AtMost1D<f32>),
    R8(AtMost1D<f64>),
    Bstr(AtMost1D<String>),
    IDispatch(AtMost1D<IDispatch>),
}

impl Out {
    /// # Safety
    ///
    /// - The input `VARIANT` must be valid.
    unsafe fn from_win32(win32: VARIANT) -> crate::Result<Self> {
        return match win32.Anonymous.Anonymous.vt {
            VT_EMPTY => Ok(Self::Empty),
            VT_BOOL => Ok(Self::Bool(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.boolVal.into(),
            ))),
            VT_UI2 => Ok(Self::Ui2(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.uiVal,
            ))),
            VT_UI4 => Ok(Self::Ui4(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.ulVal,
            ))),
            VT_UI8 => Ok(Self::Ui8(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.ullVal,
            ))),
            VT_UINT => Ok(Self::Uint(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.uintVal,
            ))),
            VT_I2 => Ok(Self::I2(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.iVal,
            ))),
            VT_I4 => Ok(Self::I4(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.lVal,
            ))),
            VT_I8 => Ok(Self::I8(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.llVal,
            ))),
            VT_INT => Ok(Self::Int(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.intVal,
            ))),
            VT_R4 => Ok(Self::R4(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.fltVal,
            ))),
            VT_R8 => Ok(Self::R8(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.dblVal,
            ))),
            VT_BSTR => Ok(Self::Bstr(AtMost1D::D0(
                win32.Anonymous.Anonymous.Anonymous.bstrVal.to_string(),
            ))),
            VT_DISPATCH => Ok({
                let win32 = ManuallyDrop::into_inner(win32.Anonymous.Anonymous);
                let win32 = ManuallyDrop::into_inner(win32.Anonymous.pdispVal).unwrap();
                Self::IDispatch(AtMost1D::D0(win32))
            }),
            vt if vt.0 & VT_ARRAY.0 != 0 => {
                let array = win32.Anonymous.Anonymous.Anonymous.parray.read_unaligned();

                if array.cDims != 1 {
                    todo!();
                }

                if vt.0 == VT_ARRAY.0 | VT_UI2.0 {
                    Ok(Self::Ui2(AtMost1D::D1(read_d1(&array).to_owned())))
                } else if vt.0 == VT_ARRAY.0 | VT_UI4.0 {
                    Ok(Self::Ui4(AtMost1D::D1(read_d1(&array).to_owned())))
                } else if vt.0 == VT_ARRAY.0 | VT_UI8.0 {
                    Ok(Self::Ui8(AtMost1D::D1(read_d1(&array).to_owned())))
                } else if vt.0 == VT_ARRAY.0 | VT_I2.0 {
                    Ok(Self::I2(AtMost1D::D1(read_d1(&array).to_owned())))
                } else if vt.0 == VT_ARRAY.0 | VT_I4.0 {
                    Ok(Self::I4(AtMost1D::D1(read_d1(&array).to_owned())))
                } else if vt.0 == VT_ARRAY.0 | VT_I8.0 {
                    Ok(Self::I8(AtMost1D::D1(read_d1(&array).to_owned())))
                } else if vt.0 == VT_ARRAY.0 | VT_R4.0 {
                    Ok(Self::R4(AtMost1D::D1(read_d1(&array).to_owned())))
                } else if vt.0 == VT_ARRAY.0 | VT_R8.0 {
                    Ok(Self::R8(AtMost1D::D1(read_d1(&array).to_owned())))
                } else if vt.0 == VT_ARRAY.0 | VT_BSTR.0 {
                    Ok(Self::Bstr(AtMost1D::D1(
                        read_d1::<BSTR>(&array)
                            .iter()
                            .map(ToString::to_string)
                            .collect(),
                    )))
                } else if vt.0 == VT_ARRAY.0 | VT_DISPATCH.0 {
                    Ok(Self::IDispatch(AtMost1D::D1(read_d1(&array).to_owned())))
                } else {
                    Err(ErrorRepr::UnsupportedDataType(DebugMessage::from_debug(vt)).into())
                }
            }
            vt => Err(ErrorRepr::UnsupportedDataType(DebugMessage::from_debug(vt)).into()),
        };

        unsafe fn read_d1<T>(array: &SAFEARRAY) -> &[T] {
            slice::from_raw_parts(array.pvData as *const T, array.rgsabound[0].cElements as _)
        }
    }

    pub fn into_idispatch(self) -> crate::Result<IDispatch> {
        match self {
            Self::IDispatch(AtMost1D::D0(disp)) => Ok(disp),
            _ => todo!(),
        }
    }
}

impl TryFrom<Out> for () {
    type Error = crate::Error;

    fn try_from(out: Out) -> std::result::Result<Self, Self::Error> {
        match out {
            Out::Empty => Ok(()),
            out => Err(ErrorRepr::UnexpectedType(DebugMessage::from_debug(out)).into()),
        }
    }
}

macro_rules! try_from_out {
    ($({$($variant:path),*} => $ty:ty;)*) => {
        $(
            impl TryFrom<Out> for $ty {
                type Error = crate::Error;

                fn try_from(out: Out) -> std::result::Result<Self, Self::Error> {
                    match out {
                        $(
                        $variant(AtMost1D::D0(x)) => Ok(x),
                        )*
                        out => Err(ErrorRepr::UnexpectedType(DebugMessage::from_debug(out)).into()),
                    }
                }
            }


            impl TryFrom<Out> for Vec<$ty> {
                type Error = crate::Error;

                fn try_from(out: Out) -> std::result::Result<Self, Self::Error> {
                    match out {
                        $(
                        $variant(AtMost1D::D1(xs)) => Ok(xs),
                        )*
                        out => Err(
                            ErrorRepr::UnexpectedType(DebugMessage::from_debug(out)).into(),
                        ),
                    }
                }
            }
        )*
    };
}

try_from_out! {
    {Out::Bool} => bool;
    {Out::Ui2} => u16;
    {Out::Ui4, Out::Uint} => u32;
    {Out::Ui8} => u64;
    {Out::I2} => i16;
    {Out::I4, Out::Int} => i32;
    {Out::I8} => i64;
    {Out::R4} => f32;
    {Out::R8} => f64;
    {Out::Bstr} => String;
    {Out::IDispatch} => IDispatch;
}

#[derive(Debug)]
pub enum AtMost1D<T> {
    D0(T),
    D1(Vec<T>),
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
#[error(transparent)]
pub struct Error(#[from] ErrorRepr);

impl From<Infallible> for Error {
    fn from(_: Infallible) -> Self {
        unreachable!();
    }
}

impl From<windows::core::Error> for Error {
    fn from(err: windows::core::Error) -> Self {
        ErrorRepr::from(err).into()
    }
}

#[derive(Debug, Error)]
enum ErrorRepr {
    #[error(transparent)]
    Windows(#[from] windows::core::Error),

    #[error("unsupported data type: {_0:?}")]
    UnsupportedDataType(DebugMessage),

    #[error("unexpected type: {_0:?}")]
    UnexpectedType(DebugMessage),
}

struct DebugMessage {
    plain: String,
    alternated: String,
}

impl DebugMessage {
    fn from_debug(x: impl Debug) -> Self {
        Self {
            plain: format!("{x:?}"),
            alternated: format!("{x:#?}"),
        }
    }
}

impl Debug for DebugMessage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = if f.alternate() {
            &self.alternated
        } else {
            &self.plain
        };
        write!(f, "{msg}")
    }
}
