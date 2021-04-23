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

Goals:

We try to obey the rule of small numbers and make sure single digit numbers are especially fast.

| type | std worst time ns | atoi_radix10 worst ns | notes              
| u8   | 6                 | 3.8                   |
| i8   | 8.1               | 5                     |
| u16  | 6.8               | 5.1                   |
| i16  | 8                 | 5.5                   |
| u32  | 14                | 7                     |
| i32  | 10                | 8                     | (+/-8 chars worst) 
| u64  | 24                | 12                    |                    
| i64  | 21                | 12                    |
| u128 | 96                | 25                    |
| i128 | 360               | 25                    |

How this works
==============
This is called SWAR: Simd within a register.

Optimisations that didn't
=========================
Things that didn't seem to have any effect:

   * casting len from usize to u8.

TODO
====

   * fuzz
   * does it work on opposite-endien than x86?