# Inert

This is a mechanism to access non-`Sync` values in `Sync` contexts.

## How is this sound?

When the user create a `&Inert<T>` value from a `&T`, they must swear on the
holy baguette that they won't use the `T` directly until all the `Inert`
wrappers go out of scope, while the various implementations of the `Neutralize`
trait make sure that the non-`Sync` behaviour of the `T` cannot be observed
through the wrapper.

## How can I help?

Improve documentation, review the code (most importantly everything because
everything is unsafe), make use of it.
