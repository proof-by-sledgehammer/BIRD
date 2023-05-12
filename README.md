# BIRD

This is the Coq code correspoding to the paper "BIRD: A Binary IR for formally verified Decompilation".

This code mirrors the paper as follows:
- Utility functionality as described at the start of section 3 is in `Bits.v` and `Util.v`
- Section 3.1 is implemented in `GenericSyntax.v` and `GenericSemantics.v`
- Section 3.2 is implemented in `X86Syntax.v` and `X86Semantics.v`
- Section 3.3 is implemented in `EarlyBirdSyntax.v` and `EarlyBirdSemantics.v`
- Section 4   is implemented in `Reg2Var.v`

# Requirements

- OCaml version 4.12.0
- Coq version 8.13.1
- coq-bits version 1.1.0

# Building

Running `make` runs all proofs and generates the Haskell output.
Note that some of the proofs take around a minute to run.
