From Coq Require Import ssreflect.

From BIRD Require Import Bits.

Class EqDec (T : Type) :=
  eqb : T -> T -> bool.

Class IsCell (C A : Type) :=
  cell_word_pattern : C -> A -> pattern.

Definition cell_word_size {C A} `{IsCell C A} c a := pattern_word_size (cell_word_pattern c a).
Definition cell_word_type {C A} `{IsCell C A} c a := pattern_word_type (cell_word_pattern c a).

Class IsLabel (L : Type) :=
  { label_value : L -> qword ; label_unvalue : qword -> L }.

Definition option_bind {A B : Type} (f : A -> option B) (o : option A) : option B :=
  if o is Some a then f a else None.
