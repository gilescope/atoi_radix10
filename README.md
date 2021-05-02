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

+/- 0000000000000 then numbers.

Goals:

An exploration of the fastest way to parse numbers without reading memory that you don't own. (Once happy with the result we can try and de-unsafe as much as possible
while keeping the performance.)

We try to obey the rule of small numbers and make sure single digit numbers are especially fast, and in general all numbers will be parsed faster than std.

| type | std worst time ns | atoi_radix10 worst ns | std best | ati best |
| u8   | 6                 | 3.8                   | 3.2      | 2.0      |
| i8   | 8.1               | 5                     |
| u16  | 6.8               | 5.1                   |
| i16  | 8                 | 5.5                   |
| u32  | 14                | 7                     |
| i32  | 10                | 8                     |
| u64  | 24                | 12                    |
| i64  | 21                | 12                    |
| u128 | 96                | 25                    |
| i128 | 360               | 25                    |

(worst doesn't include leading + and leading 000s as these aren't typical)

How this works
==============
This is called SWAR: Simd within a register.

Optimisations that did help
===========================

   * Taking an if is faster than not.
   * Moving `+` further up before it was accessed due to latency requirements.
   * Try not to do any instructions requiring latency just before returning. For example `if cond { return a as u16 }`, you can calculate the `a as u16` before the if then it's faster. (We're optimising for the happy path)

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