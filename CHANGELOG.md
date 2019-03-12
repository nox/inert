# 0.2.4

The most notable change in this release is that impls of `NeutralizeUnsafe` for
things like `(A, B)` don't require `A` to be `NeutralizeUnsafe` itself anymore,
which means that `(A, B)` can be neutralised even if some of its fields aren't.

Furthermore, if those fields aren't `NeutralizeUnsafe` but are `Sync`, users
can still safely access their contents through `Inert::get_ref`.

## Other changes

* Made the getters be `#[inline]`, thanks Rémy Rakić!
* Fixed a span which would make the code not build with `#[deny(unsafe_code)]`.

# inert_derive 0.1.2

* Decorated the inert getters with `#[allow(unsafe_code)]`.

# 0.2.3

* Introduced `inert::Neutralized<T>`.
* Implemented `#[inert::neutralize(as vis? unsafe InertFoo)]`.

# 0.2.2

* Implemented `#[inert::neutralize(as Self)]`.

# 0.2.1

* Tweaked some documentation.
* Added a test based on a tree of `RefCell<T>` values.

# 0.2.0

Let's try to document a bit what the hell we are doing here. 👀

## Breaking changes

* Renamed `Neutralize` to `NeutralizeUnsafe`.
* Renamed `Inert::from_ref` to `Inert::new_unchecked`.

## Non-breaking changes

* Added some documentation.
* Implemented `Eq`, `Ord`, `Debug` and `Display` for `Inert<T>`.
* Implemented `NeutralizeUnsafe` for `core::cell::Cell<T>`.
* Implemented `NeutralizeUnsafe` for `std::sync::Weak<T>`.
* Introduced safe ways to neutralize with `Inert::new` and `Inert::new_mut`.

# 0.1.0

Initial release! No documentation, no tests, only 🥖
