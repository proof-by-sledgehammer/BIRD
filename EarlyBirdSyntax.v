From Coq Require Import ssreflect.
From Coq Require Import String.

From BIRD Require Import Bits Util GenericSyntax.

From Bits Require Import bits.
From mathcomp Require Import eqtype tuple.

(******************************************************************************)
(*** VARIABLES                                                                *)
(******************************************************************************)

Section VARIABLES.

  Variant bird_variable_kind :=
    | bird_register_variable
    | bird_local_variable
    | bird_global_variable
  .

  Record bird_variable :=
    { bird_var_name  : string
    ; bird_var_index : option nat
    ; bird_var_kind  : bird_variable_kind
    }.

  Record bird_variable_annot :=
    { bird_var_pattern : pattern
    }.

  Definition bird_variable_kind_eq_dec (k1 k2 : bird_variable_kind) : {k1 = k2} + {k1 <> k2}.
  Proof. decide equality. Defined.

  Definition bird_variable_eq_dec (v1 v2 : bird_variable) : {v1 = v2} + {v1 <> v2}.
  Proof.
    destruct v1 as [n1 i1 k1], v2 as [n2 i2 k2].
    (* Check kinds *)
    case (bird_variable_kind_eq_dec k1 k2) ; last (right ; now injection 1).
    intro kinds_equal.
    (* Check names *)
    case (String.eqb n1 n2) eqn:Hn ; last (right ; apply eqb_neq in Hn ; now injection 1).
    apply eqb_eq in Hn as nams_equal.
    (* Check indices options *)
    case i1 as [i1|], i2 as [i2|]; last (left ; now subst).
    2,3: right ; now injection 1.
    (* Check indices *)
    case (PeanoNat.Nat.eq_dec i1 i2) ; last (right ; now injection 1).
    left ; now subst.
  Defined.

  Definition bird_variable_eqb (v1 v2 : bird_variable) : bool :=
    if bird_variable_eq_dec v1 v2 is left _ then true else false.


End VARIABLES.

Instance bird_var_IsCell : IsCell bird_variable bird_variable_annot :=
  { cell_word_pattern := fun _ a => bird_var_pattern a }.

Instance bird_var_EqDec : EqDec bird_variable :=
  { eqb := bird_variable_eqb }.

(******************************************************************************)
(*** LABELS                                                                   *)
(******************************************************************************)

Section LABELS.

  Local Open Scope bool_scope.

  Definition bird_label := qword.

  Instance bird_label_EqDec : EqDec bird_label :=
    { eqb := fun a b => a == b }.

End LABELS.

(******************************************************************************)
(*** INSTANTIATIONS                                                           *)
(******************************************************************************)

Notation bird_addr_expr       := (addr_expr bird_variable).
Notation bird_addr            := (addr bird_variable).
Notation bird_source          := (source bird_variable bird_variable_annot).
Notation bird_destination     := (destination bird_variable bird_variable_annot).
Notation bird_instruction     := (instruction bird_variable bird_variable_annot bird_label).
Notation bird_phi_instruction := (phi_instruction bird_variable).
Notation bird_phi_block       := (phi_block bird_variable).
Notation bird_code            := (code bird_variable bird_variable_annot bird_label).
Notation bird_phicode         := (phicode bird_variable bird_label).
Notation bird_program         := (program bird_variable bird_variable_annot bird_label).
Notation bird_node            := (node bird_variable bird_variable_annot bird_label).
