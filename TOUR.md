## Cryptol Semantics

This repository contains a Coq model for some of the semantics of the
Cryptol language. It is not (at this point) meant to be a complete
model of the langauge, as there are lots of language features left
unmodeled. However, enough of the language has been modeled that this
model has been used to verify HMAC, One Time Pad, and a decent amount
of progress has been made towards verifying SHA256.

The files specific towards these three verification efforts are in the
HMAC, SHA256, and OTP directories respectively. The main development
is kept in the src directory, which is the only directory strictly
necessary to start verifying an additional cryptol program.

There are several make targets. In order to build just the src
directory, use the default make target. In order to build everything,
use the verif make target. Build in parallel whenever possible.

## Eager and Lazy

One of the key insights of this project is that it is much easier to
reason about a cryptol program in an eager setting, than in a lazy one.




Authored by Eric Mullen, August 2017.