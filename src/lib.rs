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

#[cfg(feature = "std")]
extern crate core;

use core::ops::Deref;

#[cfg(feature = "std")]
use std::borrow::Cow;
#[cfg(feature = "std")]
use std::panic::{Location, PanicInfo};

/// Unsafely neutralizes a reference, returning a `Sync` view to it.
///
/// For example, `RefCell<T>` implements it with `Output` as
/// `<T as NeutralizeUnsafe>::Output`, accessing the inner value of the
/// cell directly through `RefCell::as_ptr`.
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
/// If `T` is `NeutralizeUnsafe`, this type derefs to
/// `<T as NeutralizeUnsafe>::Output`,
/// with no safe way to reach out for the `T` value itself, which is why
/// it is sound for `Inert<T>` to be `Sync`.
#[repr(transparent)]
pub struct Inert<T: ?Sized> {
    value: T,
}
unsafe impl<T> Sync for Inert<T> where T: ?Sized {}

impl<T> Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    /// Unsafely creates a new `Inert<T>` from a reference.
    ///
    /// # Safety
    ///
    /// The user must swear on the holy baguette that they won't do anything
    /// with the `&T` as long as any thread is still doing things with the
    /// `&Inert<T>`, either directly or through other neutralized values
    /// reached through the inner `&<T as NeutralizeUnsafe>::Output` value, lest
    /// they provoke undefined behaviour, or worse, spoil their entire wheat
    /// harvest.
    #[inline]
    pub unsafe fn new_unchecked(value: &T) -> &Self {
        &*(value as *const T as *const Self)
    }
}

impl<T> Deref for Inert<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Target = T::Output;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.value.neutralize_unsafe() }
    }
}

unsafe impl<'a, T> NeutralizeUnsafe for &'a T
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = <T as NeutralizeUnsafe>::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        T::neutralize_unsafe(self)
    }
}

unsafe impl<'a, T> NeutralizeUnsafe for &'a mut T
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = <T as NeutralizeUnsafe>::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        T::neutralize_unsafe(self)
    }
}

unsafe impl<T> NeutralizeUnsafe for core::cell::Cell<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = <T as NeutralizeUnsafe>::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        (*self.as_ptr()).neutralize_unsafe()
    }
}

unsafe impl<T> NeutralizeUnsafe for core::cell::RefCell<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = <T as NeutralizeUnsafe>::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        (*self.as_ptr()).neutralize_unsafe()
    }
}

unsafe impl<'a, T> NeutralizeUnsafe for core::cell::Ref<'a, T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = <T as NeutralizeUnsafe>::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        T::neutralize_unsafe(self)
    }
}

unsafe impl<'a, T> NeutralizeUnsafe for core::cell::RefMut<'a, T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = <T as NeutralizeUnsafe>::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        T::neutralize_unsafe(self)
    }
}

#[cfg(feature = "std")]
unsafe impl<T> NeutralizeUnsafe for std::rc::Rc<T>
where
    T: ?Sized + NeutralizeUnsafe,
{
    type Output = <T as NeutralizeUnsafe>::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        T::neutralize_unsafe(self)
    }
}

#[cfg(feature = "std")]
unsafe impl<'a, T> NeutralizeUnsafe for Cow<'a, T>
where
    T: 'a + ?Sized + NeutralizeUnsafe + ToOwned,
    <T as ToOwned>::Owned: NeutralizeUnsafe<Output = <T as NeutralizeUnsafe>::Output>,
{
    type Output = <T as NeutralizeUnsafe>::Output;

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        match *self {
            Cow::Borrowed(ref this) => T::neutralize_unsafe(this),
            Cow::Owned(ref this) => {
                // We can't just deref the Cow<T> because it calls
                // <T::Owned>::borrow and <T::Owned> may not be Sync.
                <<T as ToOwned>::Owned>::neutralize_unsafe(this)
            },
        }
    }
}

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

#[cfg(feature = "std")]
unsafe impl<T> NeutralizeUnsafe for Vec<T>
where
    T: NeutralizeUnsafe,
{
    type Output = [Inert<T>];

    #[inline]
    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        <[T]>::neutralize_unsafe(self)
    }
}

macro_rules! neutralize_as_deref {
    ($($($id:ident)::* <$($param:tt),*>,)*) => {$(
        unsafe impl<$($param),*> NeutralizeUnsafe for $($id)::* <$($param),*>
        where
            $($param: ?Sized + NeutralizeUnsafe,)*
        {
            type Output = <T as NeutralizeUnsafe>::Output;

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &Self::Output {
                T::neutralize_unsafe(self)
            }
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
        $(where $($p: $($bound)*),*)* {
            type Output = Self;

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &Self::Output {
                self
            }
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
        unsafe impl <$($lt,)* $($param),*> NeutralizeUnsafe for $($id)::* <$($lt,)* $($param),*>
        where
            $($param: NeutralizeUnsafe,)*
        {
            type Output = $($id)::* <$($lt,)* $(Inert<$param>),*>;

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &Self::Output {
                &*(self as *const Self as *const Self::Output)
            }
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
