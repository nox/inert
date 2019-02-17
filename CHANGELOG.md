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
