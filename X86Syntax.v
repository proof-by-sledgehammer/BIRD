From Coq Require Import ssreflect.

From BIRD Require Import Bits Util GenericSyntax.

From Bits Require Import bits.
From mathcomp Require Import eqtype tuple.


(******************************************************************************)
(*** REGISTERS                                                                *)
(******************************************************************************)

Section REGISTERS.

  Definition x86_register_annot := unit.
  Variant x86_register :=
    | x86_rax | x86_eax | x86_ax | x86_al | x86_ah
    | x86_rbx | x86_ebx | x86_bx | x86_bl | x86_bh
    | x86_rcx | x86_ecx | x86_cx | x86_cl | x86_ch
    | x86_rdx | x86_edx | x86_dx | x86_dl | x86_dh
    | x86_rsi | x86_esi | x86_si | x86_sil
    | x86_rdi | x86_edi | x86_di | x86_dil
    | x86_rbp | x86_ebp | x86_bp | x86_bpl
    | x86_rsp | x86_esp | x86_sp | x86_spl
    | x86_r08 | x86_r08d | x86_r08w | x86_r08b
    | x86_r09 | x86_r09d | x86_r09w | x86_r09b
    | x86_r10 | x86_r10d | x86_r10w | x86_r10b
    | x86_r11 | x86_r11d | x86_r11w | x86_r11b
    | x86_r12 | x86_r12d | x86_r12w | x86_r12b
    | x86_r13 | x86_r13d | x86_r13w | x86_r13b
    | x86_r14 | x86_r14d | x86_r14w | x86_r14b
    | x86_r15 | x86_r15d | x86_r15w | x86_r15b
  .

  Definition x86_register_word_pattern (r : x86_register) : pattern :=
    match r with
    | x86_rax => full64 | x86_eax  => low32 | x86_ax   => low16 | x86_al   => low8 | x86_ah => high8
    | x86_rbx => full64 | x86_ebx  => low32 | x86_bx   => low16 | x86_bl   => low8 | x86_bh => high8
    | x86_rcx => full64 | x86_ecx  => low32 | x86_cx   => low16 | x86_cl   => low8 | x86_ch => high8
    | x86_rdx => full64 | x86_edx  => low32 | x86_dx   => low16 | x86_dl   => low8 | x86_dh => high8
    | x86_rsi => full64 | x86_esi  => low32 | x86_si   => low16 | x86_sil  => low8
    | x86_rdi => full64 | x86_edi  => low32 | x86_di   => low16 | x86_dil  => low8
    | x86_rbp => full64 | x86_ebp  => low32 | x86_bp   => low16 | x86_bpl  => low8
    | x86_rsp => full64 | x86_esp  => low32 | x86_sp   => low16 | x86_spl  => low8
    | x86_r08 => full64 | x86_r08d => low32 | x86_r08w => low16 | x86_r08b => low8
    | x86_r09 => full64 | x86_r09d => low32 | x86_r09w => low16 | x86_r09b => low8
    | x86_r10 => full64 | x86_r10d => low32 | x86_r10w => low16 | x86_r10b => low8
    | x86_r11 => full64 | x86_r11d => low32 | x86_r11w => low16 | x86_r11b => low8
    | x86_r12 => full64 | x86_r12d => low32 | x86_r12w => low16 | x86_r12b => low8
    | x86_r13 => full64 | x86_r13d => low32 | x86_r13w => low16 | x86_r13b => low8
    | x86_r14 => full64 | x86_r14d => low32 | x86_r14w => low16 | x86_r14b => low8
    | x86_r15 => full64 | x86_r15d => low32 | x86_r15w => low16 | x86_r15b => low8
    end.

  Definition x86_register_eq_dec (r1 r2 : x86_register) : {r1 = r2} + {r1 <> r2}.
  Proof. decide equality. Qed.

  Definition x86_register_eqb (r1 r2 : x86_register) :=
    if x86_register_eq_dec r1 r2 is left _ then true else false.

End REGISTERS.

Instance x86_register_EqDec : EqDec x86_register :=
  { eqb := x86_register_eqb }.

Instance x86_register_IsCell : IsCell x86_register x86_register_annot :=
  { cell_word_pattern := fun r _ => x86_register_word_pattern r }.


(******************************************************************************)
(*** LABELS                                                                   *)
(******************************************************************************)

Section LABELS.

  Local Open Scope bool_scope.

  Definition x86_label := qword.

  Instance x86_label_EqDec : EqDec x86_label :=
    { eqb := fun a b => a == b }.

End LABELS.

(******************************************************************************)
(*** INSTANTIATIONS                                                           *)
(******************************************************************************)

Notation x86_addr_expr       := (addr_expr x86_register).
Notation x86_addr            := (addr x86_register).
Notation x86_source          := (source x86_register x86_register_annot).
Notation x86_destination     := (destination x86_register x86_register_annot).
Notation x86_instruction     := (instruction x86_register x86_register_annot x86_label).
Notation x86_phi_instruction := (phi_instruction x86_register).
Notation x86_phi_block       := (phi_block x86_register).
Notation x86_code            := (code x86_register x86_register_annot x86_label).
Notation x86_phicode         := (phicode x86_register x86_label).
Notation x86_program         := (program x86_register x86_register_annot x86_label).
Notation x86_node            := (node x86_register x86_register_annot x86_label).
Notation x86_annot           := unit.
