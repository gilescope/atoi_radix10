
![CI](https://github.com/gilescope/parseint/actions/workflows/ci.yml/badge.svg)

Faster Integer Parsing (rust port)
==================================

!! This crate does work on stable but only 1.55 and above !!

This repository is the rust port of @KholdStare experimentation in
https://kholdstare.github.io/technical/2020/05/26/faster-integer-parsing.html

There is also a blog post on this in Rust Malaysia.
https://github.com/rust-malaysia/rust-malaysia.github.io/blob/master/_posts/2020-07-12-faster-integer-parsing.md

From discussions on reddit, it turns out someone else has stumbled on the exact
same ideas before @KholdStare, Wojciech Muła.
http://0x80.pl/articles/simd-parsing-int-sequences.html

Notes:

Spec:

+/- 0000000000000 then digits.

Goals:

An exploration of the fastest way to parse numbers without reading memory that you don't own. (Once happy with the result we can try and de-unsafe as much as possible
while keeping the performance.)

We try to obey the rule of small numbers and make sure single digit numbers are especially fast, and in general all numbers will be parsed faster than std.

Performance
===========

If you have to parse u128 and i128 numbers this crate does any number in under 25ns
(and if you target a specific cpu with avx then maybe all under 15ns-20ns). It is hands down many many times faster than std rust (especially i128) across all the numbers.

For u8/i8 it's about the same as std.

For u16, u32, u64 it's around 1/3 faster than std.

Usage and Features
==================

`nightly` and `simd` features for highest speed (and target your specific cpu).

It's `no_std` by default and will parse from any `[u8]` slice.

How this works
==============
This is called SWAR: Simd within a register.

Optimisations that did help
===========================

   * Using likely and unlikely intrinsics.
   * Moving `+` further up before it was accessed due to latency requirements.
   * Try not to do any instructions requiring latency just before returning. For example `if cond { return a as u16 }`, you can calculate the `a as u16` before the if then it's faster. (We're optimising for the happy path)
   * It was much easier to start fast and try and add things in than to start slow and make it faster (the latter you are in the dark as to why it is slow and just guessing, where as if you build it up you know instantly when you add something in that borks the speed.).
   * It turns out that the error enum slows things down a bit so for max speed you can `.map_err(|_| ())` if you don't care what type of parse error it is.

Optimisations that didn't
=========================
Things that didn't seem to have any effect:

   * Compiler breaks down *10 to *8 + *2 behind the scenes so we don't have to.
     (It seems to resort to imul for 100 so replacing shifts for that might make
     a slight gain)
   * casting len from usize to u8.

FAQ
===

   * Should I use this in production? As it's a new crate I would treat it with caution,
   there could still be a bug or two lurking despite tests and some light fuzzing. It's had one `reddit review` from which I've hopefully plugged a soundness hole around alignment.

   * Why not include this in the std library? The std library parsing code isn't radix specific. As the num parsing is in core, code size is important for embedded systems. This implementation is definitely more code than std.

   * If you want to run the tests under wasm you need to install:
   ```
   cargo install wasm-bindgen-cli
   ```

TODO
====

   - [x] make all the tests work in no_std mode.
   - [x] Compile for wasm
   - [ ] Bench on wasm?
   - [x] Run tests under wasm: `cargo test --features nightly --target=wasm32-unknown-unknown`
   - [x] have all wasm tests pass.
   - [ ] Wasm + Simd - can I use core simd and things just work with simulation for 256bits?
   - [ ] use no non-portable simd commands (so simd feature works on arm/neon).
   - [x] make work on big-endian

## Big-endien

We can run the tests on big-endien via MIRI:

```sh
rustup +nightly component add miri
MIRIFLAGS="-Zmiri-symbolic-alignment-check" cargo miri test --target mips64-unknown-linux-gnuabi64
```