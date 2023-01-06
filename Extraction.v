From Coq Require Import ExtrHaskellBasic.
From Coq Require Import ExtrHaskellNatNum.
From Coq Require Import ExtrHaskellString.

Extraction Language Haskell.

From BIRD Require Import Reg2Var.

Extraction "./BIRD.hs" reg2var_program.
