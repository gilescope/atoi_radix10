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

This is called SWAR: Simd within a register.