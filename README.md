# Inert

This is a mechanism to access non-`Sync` values in a `Sync` way.

## How is this sound?

When the user creates a `&Inert<T>` value from a `&T`, they must swear on the
holy baguette that they won't use the `T` directly until all the `Inert`
wrappers go away, while the various implementations of the `NeutralizeUnsafe`
trait make sure that the non-`Sync` behaviour of the `T` cannot be observed
through the wrapper.

## How can I help?

Improve documentation, test the crate, make use of it.
