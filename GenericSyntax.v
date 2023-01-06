(******************************************************************************)
(** Generic Syntax                                                            *)
(******************************************************************************)

From Bits Require Import bits.

From Coq Require Import ssreflect.
From Coq Require Import List.
Import ListNotations.

From mathcomp Require Import eqtype tuple.

From BIRD Require Import Bits Util.

Declare Scope bird_scope.
Delimit Scope bird_scope with bird.

(******************************************************************************)
(*** Memory                                                                   *)
(******************************************************************************)

Section ADDRESS.

  Local Open Scope bird.

  Let _0 : qword := (#0, #0, #0, #0, #0, #0, #0, #0).
  Let _1 : qword := (#0, #0, #0, #0, #0, #0, #0, #1).
  Let _2 : qword := (#0, #0, #0, #0, #0, #0, #0, #2).
  Let _4 : qword := (#0, #0, #0, #0, #0, #0, #0, #4).
  Let _8 : qword := (#0, #0, #0, #0, #0, #0, #0, #8).

  Variable (Cell : Type).

  Variant scale := scale1 | scale2 | scale4 | scale8.

  Definition qword_scale (v : qword) (s : scale) : qword :=
    match s with
    | scale1 => v
    | scale2 => v + v
    | scale4 => v + v + v + v
    | scale8 => v + v + v + v + v + v + v
    end.

  Definition abs_addr := qword.

  Record addr_expr := mk_addr_expr
    { expr_base   : option Cell
    ; expr_index  : option Cell
    ; expr_scale  : scale
    ; expr_offset : abs_addr
    }.

  Definition addr := (word_size * addr_expr)%type.

  Definition addr_expr_eval (e : addr_expr) (f : Cell -> qword) : abs_addr :=
    let b_val := if expr_base e is Some b_cell then f b_cell else _0 in
    let i_val := if expr_index e is Some i_cell then f i_cell else _0 in
    let d_val := expr_offset e in
    b_val + (qword_scale i_val (expr_scale e)) + d_val.

  Definition addr_word_type (a : addr) : Type :=
    match fst a with
    | BYTE  => byte
    | WORD  => word
    | DWORD => dword
    | QWORD => qword
    end.

End ADDRESS.

Arguments addr_word_type {Cell}.
Arguments addr_expr_eval {Cell}.

(******************************************************************************)
(*** FLAGS                                                                    *)
(******************************************************************************)

Section FLAGS.

  Variant flag := zero_flag | adjust_flag | carry_flag | parity_flag.

  Definition flag_eq_dec (a b : flag) : {a = b} + {a <> b}. decide equality. Defined.
  Definition flag_eqb (a b : flag) := if flag_eq_dec a b is left _ then true else false.

End FLAGS.

(******************************************************************************)
(*** STATE PART                                                               *)
(******************************************************************************)

Section STATEPART.

  Variable (Cell : Type).
  Variable (Annot : Type).

  Variant source :=
    | src_imm  of qword
    | src_addr of addr Cell
    | src_expr of addr_expr Cell
    | src_cell of Cell & Annot
    | src_rip.

  Variant destination :=
    | dst_addr of addr Cell
    | dst_cell of Cell & Annot.

End STATEPART.

(******************************************************************************)
(*** PROGRAM GRAPH                                                            *)
(******************************************************************************)

Section GRAPH.

  Variables (Cell Annot Label : Type).

  Variant opcode_1_1  := op_mov  | op_inc | op_dec | op_neg | op_not.
  Variant opcode_2_0  := op_cmp  | op_test.
  Variant opcode_2_1  := op_add  | op_sub | op_xor | op_or  | op_and.
  Variant opcode_2_2  := op_imul | op_xchg.
  Variant opcode_cond := op_jz   | op_jnz | op_js  | op_jns | op_jg | op_jge | op_jl | op_jle.

  Local Notation the_src  := (source Cell Annot).
  Local Notation the_dst  := (destination Cell Annot).

  Variant instruction (labels : list Label) :=
    | instr_nop  of                                                            { l | In l labels }
    | instr_hlt
    | instr_1_1  of opcode_1_1  & the_dst           & the_src           &      { l | In l labels }
    | instr_2_0  of opcode_2_0                      & the_src & the_src &      { l | In l labels }
    | instr_2_1  of opcode_2_1  & the_dst           & the_src & the_src &      { l | In l labels }
    | instr_2_2  of opcode_2_2  & the_dst & the_dst & the_src & the_src &      { l | In l labels }
    | instr_push of                         Cell    & Cell    & the_src &      { l | In l labels }
    | instr_pop  of               the_dst & Cell    & Cell              &      { l | In l labels }
    | instr_jmp  of                                   the_src           & list { l | In l labels }
    | instr_cjmp of opcode_cond                     & the_src           & list { l | In l labels } & { l | In l labels }
    | instr_call of                         Cell    & Cell    & the_src & list { l | In l labels } & { l | In l labels }
    | instr_ret  of                         Cell    & Cell    &           list { l | In l labels }
  .

  Definition instr_next {labels} (i : instruction labels) : list { l | In l labels } :=
    match i with
    | instr_nop            next        => [next]
    | instr_hlt                        => []
    | instr_1_1  _ _   _   next        => [next]
    | instr_2_0  _ _ _     next        => [next]
    | instr_2_1  _ _ _ _   next        => [next]
    | instr_2_2  _ _ _ _ _ next        => [next]
    | instr_push     _ _ _ next        => [next]
    | instr_pop    _ _ _   next        => [next]
    | instr_jmp        _   next        =>  next
    | instr_cjmp _     _   target next =>  next::target
    | instr_call   _ _ _   next ret    =>  ret::next
    | instr_ret      _ _   next        =>  next
    end.

  Record phi_instruction :=
    { phi_srcs : list Cell
    ; phi_dst  : Cell
    }.

  Definition phi_block := list phi_instruction.

  Definition code    (labels : list Label) := forall l, In l labels -> instruction labels.
  Definition phicode (labels : list Label) := forall l, In l labels -> phi_block.

  Record program :=
    { prog_nodes   : list Label
    ; prog_entry   : Label
    ; prog_code    : code prog_nodes
    ; prog_phicode : phicode prog_nodes
    }.

  Definition prog_nodes_instrs {p} (ns : list Label) (H : forall n, In n ns -> In n (prog_nodes p)) : list (instruction (prog_nodes p)).
    destruct p as [nodes entry code phicode] ; simpl in *.
    induction ns as [|hd tl rec].
    - exact nil.
    - apply cons.
      + apply (code hd). apply H. now left.
      + apply rec ; intros n Hn. apply H. now right.
  Defined.

  Definition prog_instrs p : list (instruction (prog_nodes p)) :=
    prog_nodes_instrs (prog_nodes p) (fun _ H => H).

  Record wf_phi (p : phi_block) : Prop :=
    { wf_phi_n : exists n, forall i, In i p -> length (phi_srcs i) = n
    }.

  Record wf_prog (p : program) : Prop :=
    { wf_prog_entry : In (prog_entry p) (prog_nodes p)
    }.

  Definition node (p : program) := { n | In n (prog_nodes p) }.

  Definition prog_nodes_nodes {p} (ns : list Label) (H : forall n, In n ns -> In  n (prog_nodes p)) : list (node p).
    unfold node.
    destruct p as [nodes entry code phicode] ; simpl in *.
    induction ns as [|hd tl rec].
    - exact nil.
    - apply cons.
      + exists hd. apply H. now left.
      + apply rec ; intros n Hn. apply H. now right.
  Defined.

  Definition prog_nodes' p : list (node p) :=
    prog_nodes_nodes (prog_nodes p) (fun _ H => H).

  Definition instr {p} (n : node p) : instruction (prog_nodes p) :=
    prog_code p (proj1_sig n) (proj2_sig n).

  Definition phi {p} (n : node p) : phi_block :=
    prog_phicode p (proj1_sig n) (proj2_sig n).

  Definition succs {p} (n : node p) : list (node p) :=
    instr_next (prog_code p (proj1_sig n) (proj2_sig n)).

  Definition is_pred {_ : EqDec Label} {p} (pred succ : node p) : bool :=
    List.existsb (fun s => eqb (proj1_sig succ) (proj1_sig s)) (instr_next (instr pred)).

  Definition preds {_ : EqDec Label} {p} (succ : node p) : list (node p) :=
    List.filter (fun pred => is_pred pred succ) (prog_nodes' p).

  Definition is_nth_predb {_ : EqDec Label} {p} (pred succ : node p) (n : nat) : bool :=
    if List.nth_error (preds succ) n is Some pred' then eqb (proj1_sig pred) (proj1_sig pred') else false.

  Definition is_nth_pred {_ : EqDec Label} {p} (pred succ : node p) (n : nat) : Prop :=
    if is_nth_predb pred succ n then True else False.

End GRAPH.
