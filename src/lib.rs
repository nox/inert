// Copyright 2018 Anthony Ramine
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! `Inert` lets you access non-`Sync` data in `Sync` context, hiding from the
//! user anything that may not be sound to use when the value is shared.

#![cfg_attr(not(feature = "std"), no_std)]

#[doc(inline)]
pub use inert_derive::neutralize;

#[cfg(feature = "std")]
extern crate core;

use core::cell::{Cell, Ref, RefCell, RefMut};
use core::cmp::Ordering;
use core::fmt;
use core::marker::PhantomData;
use core::ops::Deref;

#[cfg(feature = "std")]
use std::borrow::Cow;
#[cfg(feature = "std")]
use std::panic::{Location, PanicInfo};
#[cfg(feature = "std")]
use std::rc::Rc;

/// Marker trait for types that can be safely neutralized.
pub unsafe trait Neutralize: NeutralizeMut {}

/// Marker trait for types that can be safely neutralized mutably.
pub unsafe trait NeutralizeMut: NeutralizeUnsafe {}

/// Unsafely neutralizes a reference, returning a `Sync` view to it.
///
/// For example, `RefCell<T>` implements it with `Output` as `T::Output`,
/// accessing the inner value of the cell directly through `RefCell::as_ptr`.
pub unsafe trait NeutralizeUnsafe {
    /// The type of the `Sync` view.
    type Output: ?Sized + Sync;

    /// Unsafely neutralizes `self`.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to use `self` as long as any thread is
    /// still doing something with the return value of that method.
    unsafe fn neutralize_unsafe(&self) -> &Self::Output;
}

/// A wrapper for neutralized values.
///
/// If `T` is `Neutralize`, then it can be safely neutralized from an
/// immutable reference. Almost everything implements `Neutralize` but
/// `RefCell<T>` (and similar types).
///
/// If `T` is `NeutralizeMut`, then it can be safely neutralized from a mutable
/// reference. Almost everything implements `NeutralizeMut` but `Rc<RefCell<T>>`
/// and `&'a RefCell<T>` (and similar types).
///
/// If `T` is `NeutralizeUnsafe`, this type derefs to `T::Output`,
/// with no safe way to reach out for the `T` value itself, which is why
/// it is sound for `Inert<T>` to be `Sync`.
#[repr(transparent)]
pub struct Inert<T: ?Sized> {
    value: Neutralized<T>,
}
unsafe impl<T> Sync for Inert<T> where T: ?Sized {}

impl<T> Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    /// Creates a new `Inert<T>` from a reference.
    #[inline]
    pub fn new(value: &T) -> &Self
    where
        T: Neutralize,
    {
        unsafe { Self::new_unchecked(value) }
    }

    /// Creates a new `Inert<T>` from a mutable reference.
    #[inline]
    pub fn new_mut(value: &mut T) -> &Self
    where
        T: NeutralizeMut,
    {
        unsafe { Self::new_unchecked(value) }
    }

    /// Unsafely creates a new `Inert<T>` from a reference.
    ///
    /// # Safety
    ///
    /// The user must swear on the holy baguette that they won't do anything
    /// with the `&T` as long as any thread is still doing things with the
    /// `&Inert<T>`, either directly or through other neutralized values
    /// reached through the inner `&T::Output` value, lest they provoke
    /// undefined behaviour, or worse, spoil their entire wheat harvest.
    #[inline]
    pub unsafe fn new_unchecked(value: &T) -> &Self {
        &*(value as *const T as *const Self)
    }

    /// Returns a reference to the inner `T`.
    #[inline]
    pub fn get_ref(this: &Self) -> &T
    where
        T: Sync,
    {
        unsafe { Self::get_ref_unchecked(this) }
    }

    /// Unsafely returns a reference to the inner `T`.
    ///
    /// # Safety
    ///
    /// Undefined behaviour is possible if `T` is not `Sync`.
    #[inline]
    pub unsafe fn get_ref_unchecked(this: &Self) -> &T {
        this.value.as_ref()
    }
}

impl<T> Deref for Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Target = T::Output;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { Self::get_ref_unchecked(self).neutralize_unsafe() }
    }
}

/// A neutralized value.
///
/// Used by `#[inert::neutralize(as unsafe Foo)]`, shouldn't be needed directly.
/// Helpful nonetheless to ensure the `T` value cannot be safely accessed.
#[repr(transparent)]
pub struct Neutralized<T: ?Sized> {
    _marker: PhantomData<*mut ()>,
    value: T,
}
unsafe impl<T> Sync for Neutralized<T> where T: ?Sized {}

impl<T> Neutralized<T>
where
    T: ?Sized,
{
    /// Unsafely returns a reference to the inner `T` value.
    #[inline]
    pub unsafe fn as_ref(&self) -> &T {
        &self.value
    }
}

// Obviously everything in this crate is unsafe so it needs serious scrutiny,
// but this part especially is where all the magic happens.
//
// The following implementations are how the two safe methods `Inert::new` and
// `Inert::new_mut` are constrained to actually be sound.

unsafe impl<'a, T> NeutralizeMut for &'a T where T: ?Sized + Neutralize {}
unsafe impl<'a, T> Neutralize for &'a T where T: ?Sized + Neutralize {}

unsafe impl<'a, T> NeutralizeMut for &'a mut T where T: ?Sized + NeutralizeMut {}
unsafe impl<'a, T> Neutralize for &'a mut T where T: ?Sized + Neutralize {}

unsafe impl<T> NeutralizeMut for Cell<T> where T: ?Sized + NeutralizeMut {}

unsafe impl<T> NeutralizeMut for RefCell<T> where T: ?Sized + NeutralizeMut {}

unsafe impl<'a, T> NeutralizeMut for Ref<'a, T> where T: ?Sized + Neutralize {}
unsafe impl<'a, T> Neutralize for Ref<'a, T> where T: ?Sized + Neutralize {}

unsafe impl<'a, T> NeutralizeMut for RefMut<'a, T> where T: ?Sized + NeutralizeMut {}
unsafe impl<'a, T> Neutralize for RefMut<'a, T> where T: ?Sized + Neutralize {}

#[cfg(feature = "std")]
unsafe impl<T> NeutralizeMut for Rc<T> where T: ?Sized + Neutralize {}
#[cfg(feature = "std")]
unsafe impl<T> Neutralize for Rc<T> where T: ?Sized + Neutralize {}

#[cfg(feature = "std")]
unsafe impl<'a, T> NeutralizeMut for Cow<'a, T>
where
    T: 'a + ?Sized + Neutralize + ToOwned,
    T::Owned: NeutralizeMut<Output = T::Output>,
{
}

#[cfg(feature = "std")]
unsafe impl<'a, T> Neutralize for Cow<'a, T>
where
    T: 'a + ?Sized + Neutralize + ToOwned,
    T::Owned: Neutralize<Output = T::Output>,
{
}

// There follow all the `NeutralizeUnsafe` impls for the types that we
// mentioned in the previous important section.

unsafe impl<'a, T> NeutralizeUnsafe for &'a T
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = T::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        T::neutralize_unsafe(self)
    }
}

unsafe impl<'a, T> NeutralizeUnsafe for &'a mut T
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = T::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        T::neutralize_unsafe(self)
    }
}

unsafe impl<T> NeutralizeUnsafe for Cell<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = T::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        (*self.as_ptr()).neutralize_unsafe()
    }
}

unsafe impl<T> NeutralizeUnsafe for RefCell<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = T::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        (*self.as_ptr()).neutralize_unsafe()
    }
}

unsafe impl<'a, T> NeutralizeUnsafe for Ref<'a, T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = T::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        T::neutralize_unsafe(self)
    }
}

unsafe impl<'a, T> NeutralizeUnsafe for RefMut<'a, T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = T::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        T::neutralize_unsafe(self)
    }
}

#[cfg(feature = "std")]
unsafe impl<T> NeutralizeUnsafe for Rc<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = T::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        T::neutralize_unsafe(self)
    }
}

#[cfg(feature = "std")]
unsafe impl<'a, T> NeutralizeUnsafe for Cow<'a, T>
where
    T: 'a + ?Sized + NeutralizeUnsafe + ToOwned,
    T::Owned: NeutralizeUnsafe<Output = T::Output>,
{
    type Output = T::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        match *self {
            Cow::Borrowed(ref this) => T::neutralize_unsafe(this),
            Cow::Owned(ref this) => {
                // We can't just deref the Cow<T> because it calls
                // T::Owned::borrow and T::Owned may not be Sync.
                T::Owned::neutralize_unsafe(this)
            },
        }
    }
}

// Inert<T> implements many traits through T::Output.

impl<T> AsRef<T::Output> for Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    #[inline]
    fn as_ref(&self) -> &T::Output {
        self
    }
}

impl<T> PartialEq for Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
    T::Output: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        T::Output::eq(self, other)
    }
}

impl<T> Eq for Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
    T::Output: Eq,
{
}

impl<T> PartialOrd for Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
    T::Output: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        T::Output::partial_cmp(self, other)
    }
}

impl<T> Ord for Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
    T::Output: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        T::Output::cmp(self, other)
    }
}

impl<T> fmt::Debug for Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
    T::Output: fmt::Debug,
{
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        T::Output::fmt(self, fmt)
    }
}

impl<T> fmt::Display for Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
    T::Output: fmt::Display,
{
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        T::Output::fmt(self, fmt)
    }
}

// 🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖
// Below this sandwich are only uninteresting and trivial implementations.
// 🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖🥖

unsafe impl<T> NeutralizeUnsafe for [T]
where
    T: NeutralizeUnsafe,
{
    type Output = [Inert<T>];

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        &*(self as *const Self as *const Self::Output)
    }
}

unsafe impl<T> NeutralizeMut for [T] where T: NeutralizeMut {}
unsafe impl<T> Neutralize for [T] where T: Neutralize {}

#[cfg(feature = "std")]
unsafe impl<T> NeutralizeUnsafe for Vec<T>
where
    T: NeutralizeUnsafe,
{
    // Not `Vec<Inert<T>>` so that `Cow<[T]>` works.
    type Output = [Inert<T>];

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        <[T]>::neutralize_unsafe(self)
    }
}

#[cfg(feature = "std")]
unsafe impl<T> NeutralizeMut for Vec<T> where T: NeutralizeMut {}
#[cfg(feature = "std")]
unsafe impl<T> Neutralize for Vec<T> where T: Neutralize {}

macro_rules! neutralize_as_deref {
    ($($($id:ident)::* <$($param:tt),*>,)*) => {$(
        unsafe impl<$($param),*> NeutralizeUnsafe for $($id)::* <$($param),*>
        where
            $($param: ?Sized + NeutralizeUnsafe,)*
        {
            type Output = T::Output;

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &Self::Output {
                T::neutralize_unsafe(self)
            }
        }

        unsafe impl<$($param),*> NeutralizeMut for $($id)::* <$($param),*>
        where
            $($param: ?Sized + NeutralizeMut,)*
        {
        }

        unsafe impl<$($param),*> Neutralize for $($id)::* <$($param),*>
        where
            $($param: ?Sized + Neutralize,)*
        {
        }
    )*};
}

neutralize_as_deref! {
    core::mem::ManuallyDrop<T>,
}

#[cfg(feature = "std")]
neutralize_as_deref! {
    Box<T>,
}

#[cfg(feature = "std")]
macro_rules! neutralize_as_target {
    ($($ty:ty => $output:ty,)*) => {$(
        unsafe impl NeutralizeUnsafe for $ty {
            type Output = $output;

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &Self::Output {
                <$output>::neutralize_unsafe(self)
            }
        }

        unsafe impl NeutralizeMut for $ty {}
        unsafe impl Neutralize for $ty {}
    )*};
}

#[cfg(feature = "std")]
neutralize_as_target! {
    String => str,
    std::ffi::CString => std::ffi::CStr,
    std::ffi::OsString => std::ffi::OsStr,
    std::path::PathBuf => std::path::Path,
}

macro_rules! neutralize_as_self {
    ($($($id:ident)::* $(<$($param:tt),*>)* $(($($p:ident: ($($bound:tt)*)),*))*,)*) => {$(
        unsafe impl $(<$($param),*>)* NeutralizeUnsafe for $($id)::* $(<$($param),*>)*
        $(where
            $($p: $($bound)*),*)*
        {
            type Output = Self;

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &Self::Output {
                self
            }
        }

        unsafe impl $(<$($param),*>)* NeutralizeMut for $($id)::* $(<$($param),*>)*
        $(where
            $($p: $($bound)*),*)*
        {
        }

        unsafe impl $(<$($param),*>)* Neutralize for $($id)::* $(<$($param),*>)*
        $(where
            $($p: $($bound)*),*)*
        {
        }
    )*};
}

// Non-generic primitives.
neutralize_as_self! {
    bool,
    char, str,
    f32, f64,
    i8, i16, i32, i64, i128, isize,
    u8, u16, u32, u64, u128, usize,
}

// Sync types from libcore.
neutralize_as_self! {
    core::alloc::Layout,
    core::alloc::LayoutErr,
    core::any::TypeId,
    core::ascii::EscapeDefault,
    core::cell::BorrowError,
    core::cell::BorrowMutError,
    core::char::DecodeUtf16Error,
    core::char::EscapeDebug,
    core::char::EscapeDefault,
    core::char::EscapeUnicode,
    core::char::ParseCharError,
    core::char::ToLowercase,
    core::char::ToUppercase,
    core::cmp::Ordering,
    core::fmt::Alignment,
    core::fmt::Error,
    core::mem::Discriminant<T>,
    core::num::FpCategory,
    core::num::NonZeroU8,
    core::num::NonZeroU16,
    core::num::NonZeroU32,
    core::num::NonZeroU64,
    core::num::NonZeroU128,
    core::num::NonZeroUsize,
    core::num::ParseFloatError,
    core::num::ParseIntError,
    core::ops::RangeFull,
    core::str::CharIndices<'a>,
    core::str::Chars<'a>,
    core::str::Utf8Error,
    core::sync::atomic::AtomicBool,
    core::sync::atomic::AtomicIsize,
    core::sync::atomic::AtomicPtr<T>,
    core::sync::atomic::AtomicUsize,
    core::sync::atomic::Ordering,
    core::time::Duration,
}

// SIMD types (x86).
#[cfg(target_arch = "x86")]
neutralize_as_self! {
    core::arch::x86::CpuidResult,
    core::arch::x86::__m128,
    core::arch::x86::__m128d,
    core::arch::x86::__m128i,
    core::arch::x86::__m256,
    core::arch::x86::__m256d,
    core::arch::x86::__m256i,
}

// SIMD types (x86_64).
#[cfg(target_arch = "x86_64")]
neutralize_as_self! {
    core::arch::x86_64::CpuidResult,
    core::arch::x86_64::__m128,
    core::arch::x86_64::__m128d,
    core::arch::x86_64::__m128i,
    core::arch::x86_64::__m256,
    core::arch::x86_64::__m256d,
    core::arch::x86_64::__m256i,
}

// Sync types from libstd.
#[cfg(feature = "std")]
neutralize_as_self! {
    std::alloc::System,
    std::collections::hash_map::DefaultHasher,
    std::collections::hash_map::RandomState,
    std::env::VarError,
    std::ffi::CStr,
    std::ffi::FromBytesWithNulError,
    std::ffi::IntoStringError,
    std::ffi::NulError,
    std::ffi::OsStr,
    std::fs::DirBuilder,
    std::fs::DirEntry,
    std::fs::File,
    std::fs::FileType,
    std::fs::Metadata,
    std::fs::OpenOptions,
    std::fs::Permissions,
    std::io::Empty,
    std::io::Error,
    std::io::ErrorKind,
    std::io::Repeat,
    std::io::SeekFrom,
    std::io::Sink,
    std::io::Stderr,
    std::io::StderrLock<'a>,
    std::io::Stdin,
    std::io::StdinLock<'a>,
    std::io::Stdout,
    std::io::StdoutLock<'a>,
    std::net::AddrParseError,
    std::net::Incoming<'a>,
    std::net::IpAddr,
    std::net::Ipv4Addr,
    std::net::Ipv6Addr,
    std::net::Shutdown,
    std::net::SocketAddr,
    std::net::SocketAddrV4,
    std::net::SocketAddrV6,
    std::net::TcpListener,
    std::net::TcpStream,
    std::net::UdpSocket,
    std::panic::Location<'a>,
    std::path::Ancestors<'a>,
    std::path::Components<'a>,
    std::path::Display<'a>,
    std::path::Iter<'a>,
    std::path::Path,
    std::path::PrefixComponent<'a>,
    std::path::StripPrefixError,
    std::process::Child,
    std::process::ChildStderr,
    std::process::ChildStdin,
    std::process::ChildStdout,
    std::process::ExitStatus,
    std::process::Output,
    std::process::Stdio,
    std::sync::Arc<T> (T: (?Sized + Send + Sync)),
    std::sync::Barrier,
    std::sync::BarrierWaitResult,
    std::sync::Condvar,
    std::sync::Mutex<T> (T: (?Sized + Send)),
    std::sync::MutexGuard<'a, T> (T: (?Sized + Sync)),
    std::sync::Once,
    std::sync::PoisonError<T> (T: (Sync)),
    std::sync::RwLockReadGuard<'a, T> (T: (?Sized + Sync)),
    std::sync::RwLockWriteGuard<'a, T> (T: (?Sized + Sync)),
    std::sync::TryLockError<T> (T: (Sync)),
    std::sync::WaitTimeoutResult,
    std::sync::Weak<T> (T: (?Sized + Send + Sync)),
    std::sync::mpsc::RecvError,
    std::sync::mpsc::RecvTimeoutError,
    std::sync::mpsc::SendError<T> (T: (Sync)),
    std::sync::mpsc::SyncSender<T> (T: (Send)),
    std::sync::mpsc::TryRecvError,
    std::sync::mpsc::TrySendError<T> (T: (Sync)),
    std::thread::AccessError,
    std::thread::Builder,
    std::thread::JoinHandle<T>,
    std::thread::LocalKey<T>,
    std::thread::Thread,
    std::thread::ThreadId,
    std::time::Instant,
    std::time::SystemTime,
    std::time::SystemTimeError,
}

macro_rules! neutralize_array {
    ($($len:expr,)*) => {$(
        unsafe impl<T> NeutralizeUnsafe for [T; $len]
        where
            T: NeutralizeUnsafe,
        {
            type Output = [Inert<T>; $len];

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &Self::Output {
                &*(self as *const Self as *const Self::Output)
            }
        }
    )*}
}

neutralize_array! {
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
}

macro_rules! neutralize_tuple {
    ($(($($p:ident),*),)*) => {$(
        unsafe impl<$($p),*> NeutralizeUnsafe for ($($p,)*)
        where
            $($p: NeutralizeUnsafe,)*
        {
            type Output = ($(Inert<$p>),*);

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &Self::Output {
                &*(self as *const Self as *const Self::Output)
            }
        }

        unsafe impl<$($p),*> NeutralizeMut for ($($p,)*)
        where
            $($p: NeutralizeMut,)*
        {
        }

        unsafe impl<$($p),*> Neutralize for ($($p,)*)
        where
            $($p: Neutralize,)*
        {
        }
    )*}
}

neutralize_tuple! {
    (),
    (A),
    (A, B),
    (A, B, C),
    (A, B, C, D),
    (A, B, C, D, E),
    (A, B, C, D, E, F),
    (A, B, C, D, E, F, G),
    (A, B, C, D, E, F, G, H),
    (A, B, C, D, E, F, G, H, I),
    (A, B, C, D, E, F, G, H, I, J),
    (A, B, C, D, E, F, G, H, I, J, K),
    (A, B, C, D, E, F, G, H, I, J, K, L),
}

macro_rules! neutralize_as_ptr_cast {
    ($($($id:ident)::* <$($lt:lifetime,)* $($param:ident),*>,)*) => {$(
        unsafe impl<$($lt,)* $($param),*> NeutralizeUnsafe for $($id)::* <$($lt,)* $($param),*>
        where
            $($param: NeutralizeUnsafe,)*
        {
            type Output = $($id)::* <$($lt,)* $(Inert<$param>),*>;

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &Self::Output {
                &*(self as *const Self as *const Self::Output)
            }
        }

        unsafe impl<$($lt,)* $($param),*> NeutralizeMut for $($id)::* <$($lt,)* $($param),*>
        where
            $($param: NeutralizeMut,)*
        {
        }

        unsafe impl<$($lt,)* $($param),*> Neutralize for $($id)::* <$($lt,)* $($param),*>
        where
            $($param: Neutralize,)*
        {
        }
    )*};
}

neutralize_as_ptr_cast! {
    Option<T>,
    Result<T, E>,
    core::cmp::Reverse<T>,
    core::hash::BuildHasherDefault<H>,
    core::ops::Bound<T>,
    core::ops::Range<Idx>,
    core::ops::RangeFrom<Idx>,
    core::ops::RangeInclusive<Idx>,
    core::ops::RangeTo<Idx>,
    core::ops::RangeToInclusive<Idx>,
    core::num::Wrapping<T>,
    core::slice::Chunks<'a, T>,
    core::slice::ChunksExact<'a, T>,
    core::slice::Iter<'a, T>,
    core::slice::RChunks<'a, T>,
    core::slice::RChunksExact<'a, T>,
}

#[cfg(feature = "std")]
neutralize_as_ptr_cast! {
    std::collections::binary_heap::BinaryHeap<T>,
    std::collections::binary_heap::Iter<'a, T>,
    std::collections::btree_map::BTreeMap<K, V>,
    std::collections::btree_map::Entry<'a, K, V>,
    std::collections::btree_map::Iter<'a, K, V>,
    std::collections::btree_map::Keys<'a, K, V>,
    std::collections::btree_map::OccupiedEntry<'a, K, V>,
    std::collections::btree_map::Range<'a, K, V>,
    std::collections::btree_map::VacantEntry<'a, K, V>,
    std::collections::btree_set::BTreeSet<T>,
    std::collections::btree_set::Iter<'a, T>,
    std::collections::btree_set::Range<'a, T>,
    std::collections::hash_map::HashMap<K, V, S>,
    std::collections::hash_map::Iter<'a, K, V>,
    std::collections::hash_map::Keys<'a, K, V>,
    std::collections::hash_map::Values<'a, K, V>,
    std::collections::hash_set::HashSet<T, S>,
    std::collections::hash_set::Iter<'a, T>,
    std::collections::linked_list::Iter<'a, T>,
    std::collections::linked_list::LinkedList<T>,
    std::collections::vec_deque::Iter<'a, T>,
    std::collections::vec_deque::VecDeque<T>,
    std::io::BufReader<R>,
    std::io::Chain<T, U>,
    std::io::Cursor<T>,
    std::io::IntoInnerError<W>,
    std::io::Take<T>,
    std::iter::Chain<A, B>,
    std::iter::Cycle<I>,
    std::iter::Empty<T>,
    std::iter::Enumerate<I>,
    std::iter::Fuse<I>,
    std::iter::Once<T>,
    std::iter::Rev<I>,
    std::iter::Skip<I>,
    std::iter::StepBy<I>,
    std::iter::Take<I>,
    std::iter::Zip<A, B>,
    std::panic::AssertUnwindSafe<T>,
}

#[cfg(feature = "std")]
unsafe impl<'a> NeutralizeUnsafe for PanicInfo<'a> {
    type Output = InertPanicInfo<'a>;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        &*(self as *const Self as *const Self::Output)
    }
}

#[cfg(feature = "std")]
unsafe impl<'a> NeutralizeMut for PanicInfo<'a> {}

#[cfg(feature = "std")]
unsafe impl<'a> Neutralize for PanicInfo<'a> {}

/// An inert version of `std::panic::PanicInfo<'a>`.
#[cfg(feature = "std")]
pub struct InertPanicInfo<'a> {
    value: PanicInfo<'a>,
}
#[cfg(feature = "std")]
unsafe impl<'a> Sync for InertPanicInfo<'a> {}

#[cfg(feature = "std")]
impl<'a> InertPanicInfo<'a> {
    /// Returns the location of the panic.
    #[inline]
    pub fn location(&self) -> Option<&Location> {
        self.value.location()
    }
}

// TODO(nox): https://github.com/rust-lang/rust/pull/58369
//
// * std::collections::hash_map::Entry
// * std::collections::hash_map::OccupiedEntry
// * std::collections::hash_map::VacantEntry
