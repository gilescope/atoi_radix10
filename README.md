Faster Integer Parsing (rust port)
==================================

This repository is the rust port of @KholdStare experimentation in
https://kholdstare.github.io/technical/2020/05/26/faster-integer-parsing.html

There is also a blog post on this in Rust Malaysia.
https://rust-malaysia.github.io/code/2020/07/12/faster-integer-parsing.html

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

If you have to parse u128 and i128 numbers this crate does any number in under 20ns
(and if you target a specific cpu with avx then maybe all under 15ns). It is hands down many many times faster than std rust (especially i128) across all the numbers.

For u8/i8 it's about the same as std.

For u16, u32, u64 it's around 1/3 faster than std.

Usage and Features
==================

`nightly` and `simd` features for highest speed.

`std` feature required if you want to run all the tests. 
It's `no_std` by default and will parse from any `[u8]` slice.

How this works
==============
This is called SWAR: Simd within a register.

Optimisations that did help
===========================

   * Taking an if is faster than not.
   * Moving `+` further up before it was accessed due to latency requirements.
   * Try not to do any instructions requiring latency just before returning. For example `if cond { return a as u16 }`, you can calculate the `a as u16` before the if then it's faster. (We're optimising for the happy path)
   * It was much easier to start fast and try and add things in than to start slow and make it faster (the latter you are in the dark as to why it is slow and just guessing, where as if you build it up you know instantly when you add something in that borks the speed.).

Optimisations that didn't
=========================
Things that didn't seem to have any effect:

   * Compiler breaks down *10 to *8 + *2 behind the scenes so we don't have to.
     (It seems to resort to imul for 100 so replacing shifts for that might make
     slight gain)
   * casting len from usize to u8.

TODO
====

   * more cargo-fuzz
   * github actions CI
   * make work on big-endian ( See https://github.com/BurntSushi/rust-memchr/commit/059d0c63d30a37783b9a98bef7daf780524a3a6e )