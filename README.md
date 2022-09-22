# not_empty

Slices and vectors that are statically guaranteed to be not empty.

[![Build Status]][actions]
[![Latest Version]][crates.io]

This crate is particularly useful for various operations on slices or vectors
that would otherwise return an option now return the value with no performance
penalty.

[Build Status]: https://img.shields.io/github/workflow/status/seancroach/not_empty/ci?logo=github
[actions]: https://github.com/seancroach/not_empty/actions/workflows/ci.yml
[Latest Version]: https://img.shields.io/crates/v/not_empty?logo=rust
[crates.io]: https://crates.io/crates/not_empty

## Usage

This crate is [on crates.io][crates] and can be used by adding `not_empty`
to your dependencies in your project's `Cargo.toml`:

```toml
[dependencies]
not_empty = "0.1"
```

[crates]: https://crates.io/crates/not_empty

## Features

- `alloc` enables the use of allocated types through the alloc crate.
- `serde` enables the use of the `serde` crate to serialize and deserialize
  any `not_empty` types.
- `std` enables the use of the standard library.

*Note*: A compiler error is thrown if both `alloc` and `std` features are
enabled. Only choose up to one.

Only the `std` feature is enabled by default.

## Motivation

There are other packages that solve this solution. When searching for my own,
I came across two other packages:

* [`nonempty`] which only supported vectors and didn't have a sollution to
  working elegantly with iterators. Also, interoperability between its exported
  `NonEmpty` type and other slices or vectors left much to be desired from an
  architectural support. To be pedantic, I was jaded that the `NonEmpty` type
  was larger than a standard vector for non-zero sized types.
* [`non-empty-vec`] did not enlarge the type, which was good, but it did not
  meet my needs for interoperability as well.

[`nonempty`]: https://docs.rs/nonempty
[`non-empty-vec`]: https://docs.rs/non-empty-vec

## License

Licensed under either of

-   Apache License, Version 2.0
    ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
-   MIT license
    ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
