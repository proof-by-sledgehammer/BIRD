(******************************************************************************)
(** Generic Semantics                                                         *)
(******************************************************************************)

From Coq Require Import ssreflect.
From Coq Require Import List.
Import ListNotations.

From Bits Require Import bits.
From mathcomp Require Import eqtype tuple.

From BIRD Require Import Bits Util.
From BIRD Require Import GenericSyntax.

Declare Scope bird_scope.
Delimit Scope bird_scope with bird.

(******************************************************************************)
(*** STATE PART                                                               *)
(******************************************************************************)

Section STATEPART.

  Variable (Cell : Type).
  Variable (Annot : Type).

  Local Notation the_src := (source Cell Annot).
  Local Notation the_dst := (destination Cell Annot).

  Definition source_word_size `{IsCell Cell Annot} (src : the_src) : word_size :=
    match src with
    | src_imm  _   => QWORD
    | src_addr a   => fst a
    | src_expr e   => QWORD
    | src_cell c a => cell_word_size c a
    | src_rip      => QWORD
    end.

  Definition destination_word_size `{IsCell Cell Annot} (dst : the_dst) : word_size :=
    match dst with
    | dst_addr a   => fst a
    | dst_cell c a => cell_word_size c a
    end.

  Definition source_word_type      `{IsCell Cell Annot} (src : the_src)
    := word_type (source_word_size src).
  Definition destination_word_type `{IsCell Cell Annot} (dst : the_dst)
    := word_type (destination_word_size dst).

End STATEPART.

(******************************************************************************)
(*** STATE                                                                    *)
(******************************************************************************)

Section STATE.

  Local Open Scope bird.

  Variable (Cell Annot Label : Type).
  Context `{IsLabel Label}.

  Definition memory := abs_addr -> byte.
  Definition flags  := flag -> bit.
  Definition cells  := Cell -> qword.
  Definition rip    := Label.

  Class IsCellState `{IsCell Cell Annot} :=
      { cells_read        : cells -> forall c a, cell_word_type c a
      ; cells_write       : cells -> forall c a, cell_word_type c a -> cells
      ; cells_read_qword  : cells -> Cell -> qword
      ; cells_write_qword : cells -> Cell -> qword -> cells
      }.

  Record state := mk_state
    { state_mem   : memory
    ; state_flags : flags
    ; state_cells : cells
    ; state_rip   : rip
    }.

  Definition _0 : qword := (#0, #0, #0, #0, #0, #0, #0, #0).
  Definition _1 : qword := (#0, #0, #0, #0, #0, #0, #0, #1).
  Definition _2 : qword := (#0, #0, #0, #0, #0, #0, #0, #2).
  Definition _3 : qword := (#0, #0, #0, #0, #0, #0, #0, #3).
  Definition _4 : qword := (#0, #0, #0, #0, #0, #0, #0, #4).
  Definition _5 : qword := (#0, #0, #0, #0, #0, #0, #0, #5).
  Definition _6 : qword := (#0, #0, #0, #0, #0, #0, #0, #6).
  Definition _7 : qword := (#0, #0, #0, #0, #0, #0, #0, #7).
  Definition _8 : qword := (#0, #0, #0, #0, #0, #0, #0, #8).

  Definition memory_read (m : memory) (a : addr Cell) (f : Cell -> qword) : addr_word_type a :=
    let '(s, e) := a in
    let b (offset : abs_addr) := m ((addr_expr_eval e f) + offset) in
    match s as s' return addr_word_type (s', e) with
    | BYTE  =>                                            b _0
    | WORD  =>                                     (b _1, b _0)
    | DWORD =>                         (b _3, b _2, b _1, b _0)
    | QWORD => (b _7, b _6, b _5, b _4, b _3, b _2, b _1, b _0)
    end.

  Definition memory_write (m : memory) (a : addr Cell) (f : Cell -> qword) (v : addr_word_type a) : memory.
    destruct a as [s e].
    set e_val := addr_expr_eval e f.
    set w := fun (m : memory) (b : byte) (offset : abs_addr) a' => if a' == e_val + offset then b else m a'.
    case s eqn:?.
    - exact (w m v _0).
    - destruct v as [v0 v1].
      exact (w (w m v0 _0) v1 _1).
    - destruct v as (((v0&v1)&v2)&v3).
      exact (w (w (w (w m v0 _0) v1 _1) v2 _2) v3 _3).
    - destruct v as (((((((v0&v1)&v2)&v3)&v4)&v5)&v6)&v7).
      exact (w (w (w (w (w (w (w (w m v0 _0) v1 _1) v2 _2) v3 _3) v4 _4) v5 _5) v6 _6) v7 _7).
  Defined.

  Definition flags_read  (F : flags) (f : flag) : bit := F f.
  Definition flags_write (F : flags) (f : flag) (v : bit) : flags := fun g => if flag_eqb f g then v else F g.

  Definition state_read `{IsCellState} `{IsLabel Label}
    (s : state) (src : source Cell Annot) : source_word_type _ _ src :=
    match src as src' return source_word_type _ _ src' with
    | src_imm  i   => i
    | src_addr a   => memory_read (state_mem s) a (cells_read_qword (state_cells s))
    | src_expr e   => addr_expr_eval e (cells_read_qword (state_cells s))
    | src_cell c a => cells_read (state_cells s) c a
    | src_rip      => label_value (state_rip s)
    end.

  Definition state_read_qword `{IsCellState} `{IsLabel Label}
    (s : state) (src : source Cell Annot) : qword.
  Proof.
    set v := state_read s src.
    unfold source_word_type in v.
    unfold source_word_size in v.
    case src eqn:? ; cbn in *.
    - exact v.
    - destruct a. case w eqn:? ; cbn in v.
        + exact (insert _0 low8 v).
        + exact (insert _0 low16 v).
        + exact (insert _0 low32 v).
        + exact (insert _0 full64 v).
    - exact v.
    - exact (insert _0 (cell_word_pattern c a) v).
    - exact v.
  Defined.

  Definition state_write `{IsCellState}
    (s : state) (dst : destination Cell Annot) (v : destination_word_type _ _ dst) : state :=
    let M := state_mem s in
    let F := state_flags s in
    let C := state_cells s in
    let R := state_rip s in
    match dst as dst' return dst = dst' -> destination_word_type _ _ dst' -> state with
    | dst_addr a => fun _ v' =>
                      let mem' := memory_write (state_mem s) a (cells_read_qword (state_cells s)) v' in
                      {| state_mem := mem' ; state_flags := F ; state_cells := C ; state_rip := R |}
    | dst_cell c a => fun _ v' =>
                        let cells' := cells_write (state_cells s) c a v' in
                        {| state_cells := cells' ; state_flags := F ; state_mem := M ; state_rip := R |}
    end Logic.eq_refl v.

  Definition state_write_qword `{IsCellState} `{IsLabel Label}
    (s : state) (dst : destination Cell Annot) (v : qword) : state.
  Proof.
    set t := (destination_word_type _ _ dst).
    unfold destination_word_type in t.
    case (destination_word_size _ _ dst) eqn:F.
    - set v' := extract v low8. cbn in v'.
      have T: (byte = destination_word_type _ _ dst) by unfold destination_word_type ; rewrite F.
      exact s.
    - set v' := extract v low16. cbn in v'.
      have T: (word = destination_word_type _ _ dst) by unfold destination_word_type ; rewrite F.
      exact s.
    - set v' := extract v low32. cbn in v'.
      have T: (dword = destination_word_type _ _ dst) by unfold destination_word_type ; rewrite F.
      exact s.
    - set v' := extract v full64. cbn in v'.
      have T: (qword = destination_word_type _ _ dst) by unfold destination_word_type ; rewrite F.
      exact s.
  Defined.


  Definition state_write_rip (s : state) (r : rip) : state :=
    let M := state_mem s in
    let F := state_flags s in
    let C := state_cells s in
    mk_state M F C r.

  Definition state_inc_rip {p : program Cell Annot Label} (s : state) (i : instruction Cell Annot Label (prog_nodes _ _ _ p)) : state :=
    let rip := label_value (state_rip s) in state_write_rip s (label_unvalue (qword_add rip _8)).

End STATE.

Section DENOTATION.

  Variables (Cell Label Annot : Type).

  Local Notation the_dst := (destination Cell Annot).
  Local Notation the_src := (source Cell Annot).
  Local Notation the_state := (state Cell Annot).

  (* Few implementations for presentation purposes, other follow *)
  (* when this is integrated into the rest of the decompiler *)

  Definition computation_1_1 (opcode : opcode_1_1) : option (qword -> qword) :=
    match opcode with
    | op_inc => Some (fun a => qword_add a _1)
    | _ => None
    end.

  Definition computation_2_1 (opcode : opcode_2_1) : option (qword -> qword -> qword) :=
    match opcode with
    | op_add => Some qword_add
    | _ => None
    end.

  Definition computation_2_2 (opcode : opcode_2_2) : option (qword -> qword -> (qword * qword)%type) :=
    match opcode with
    | op_xchg => Some (fun a b => (b, a))
    | _ => None
    end.

  Definition effect_1_1 (opcode : opcode_1_1) : option (qword -> flags -> flags) :=
    match opcode with
    | op_inc => Some (fun a s => let '(c, a') := qword_addc a _1 in
                                 let s' := flags_write s zero_flag (a' == _0)%bool in
                                 flags_write s' carry_flag c
                  )
    | _ => None
    end.

  Definition effect_2_0 (opcode : opcode_2_0) : option (qword -> qword -> flags -> flags) :=
    match opcode with
    | op_cmp => Some (fun a b s => let '(b, z) := qword_subb a b in
                                   flags_write s zero_flag (negb b && (z == _0))%bool)
    | _ => None
    end.

  Definition effect_2_1 (opcode : opcode_2_1) : option (qword -> qword -> flags -> flags) :=
    match opcode with
    | op_add => Some (fun a b s => let '(c, r) := qword_addc a b in
                                  let s' := flags_write s zero_flag (r == _0)%bool in
                                 flags_write s' carry_flag c)
    | _ => None
    end.

  Definition effect_2_2 (opcode : opcode_2_2) : option (qword -> qword -> flags -> flags) :=
    match opcode with
    | op_xchg => Some (fun a b s => s)
    | _ => None
    end.

  Definition condition (op : opcode_cond) : option (flags -> bool) :=
    match op with
    | op_jnz => Some (fun fs => negb (flags_read fs zero_flag))
    | op_jz => Some (fun fs => (flags_read fs zero_flag))
    | _ => None
    end.

  Definition run_effect_1 (s : the_state) (e : qword -> flags -> flags) (v : qword) :=
    let M := state_mem _ _ s in
    let F := e v (state_flags _ _ s) in
    let C := state_cells _ _ s in
    let R := state_rip _ _ s in
    mk_state _ _ M F C R.

  Definition run_effect_2 (s : the_state) (e : qword -> qword -> flags -> flags) (v1 : qword) (v2 : qword) :=
    let M := state_mem _ _ s in
    let F := e v1 v2 (state_flags _ _ s) in
    let C := state_cells _ _ s in
    let R := state_rip _ _ s in
    mk_state _ _ M F C R.

End DENOTATION.

Section SEMANTICS.

  Variables (Cell Annot Label : Type).

  Local Notation the_prog  := (program Cell Annot Label).
  Local Notation the_instr := (instruction Cell Annot Label).
  Local Notation the_node  := (node Cell Annot Label).
  Local Notation the_state := (state Cell Label).
  Local Notation the_phis  := (phi_block Cell).
  Local Notation the_phi   := (phi_instruction Cell).
  Local Notation the_src   := (source Cell Annot).
  Local Notation the_dst   := (destination Cell Annot).

  Definition run_phi `{IsCellState Cell Annot} (n : nat) (p : the_phi) (σ : the_state) : the_state :=
    if List.nth_error (phi_srcs _ p) n is Some s
    then
      let θ  := state_mem _ _ σ in
      let ξ  := state_flags _ _ σ in
      let γ  := state_cells _ _ σ in
      let ρ  := state_rip _ _ σ in
      let v  := cells_read_qword _ _ γ s in
      let γ' := cells_write_qword _ _ γ (phi_dst _ p) v in
      mk_state _ _ θ ξ γ' ρ
    else σ.

  Fixpoint run_phis `{IsCellState Cell Annot} (n : nat) (ps : the_phis) (σ : the_state) : the_state :=
    match ps with
    | []     => σ
    | p::ps' => run_phis n ps' (run_phi n p σ)
    end.

  Inductive phi_step `{EqDec Label} `{IsCellState Cell Annot} (p : the_prog) :
    the_node p -> the_state -> the_node p -> the_state -> Prop :=
  | phi_step_block (k₁ k₂ : the_node p) (σ₁ σ₂ : the_state) n :
    is_nth_pred _ _ _ k₁ k₂ n ->
    σ₂ = run_phis n (phi _ _ _ k₂) σ₁ ->
    phi_step p k₁ σ₁ k₂ σ₂.

  Inductive instr_step `{EqDec Label} `{IsCellState Cell Annot} `{IsLabel Label} (p : the_prog) :
    the_node p -> the_state -> option (the_node p) -> the_state -> Prop :=

  | step_nop k1 k2 s1 s2 :
    instr _ _ _ k1 = instr_nop _ _ _ _ k2 ->
    s2 = state_write_rip _ _ s1 (proj1_sig k2) ->
    instr_step p k1 s1 (Some k2) s2

  | step_hlt k s :
    instr _ _ _ k = instr_hlt _ _ _ _ ->
    instr_step p k s None s

  | step_1_1 op dst src k1 k2 s1 s2 s3 s4 d f v :
    instr _ _ _ k1 = instr_1_1 _ _ _ _ op dst src k2 ->
    s2 = state_write_rip _ _ s1 (proj1_sig k2) ->
    Some d = computation_1_1 op ->
    Some f = effect_1_1 op ->
    v = state_read_qword _ _ _ s1 src ->
    s3 = state_write_qword _ _ _ s2 dst (d v) ->
    s4 = run_effect_1 _ _ s3 f v ->
    instr_step p k1 s1 (Some k2) s4

  | step_2_0 op src1 src2 k1 k2 s1 s2 s4 f v1 v2 :
    instr _ _ _ k1 = instr_2_0 _ _ _ _ op src1 src2 k2 ->
    s2 = state_write_rip _ _ s1 (proj1_sig k2) ->
    Some f = effect_2_0 op ->
    v1 = state_read_qword _ _ _ s1 src1 ->
    v2 = state_read_qword _ _ _ s1 src2 ->
    s4 = run_effect_2 _ _ s2 f v1 v2 ->
    instr_step p k1 s1 (Some k2) s4

  | step_2_1 op dst src1 src2 k1 k2 s1 s2 s3 s4 d f v1 v2 :
    instr _ _ _ k1 = instr_2_1 _ _ _ _ op dst src1 src2 k2 ->
    s2 = state_write_rip _ _ s1 (proj1_sig k2) ->
    Some d = computation_2_1 op ->
    Some f = effect_2_1 op ->
    v1 = state_read_qword _ _ _ s1 src1 ->
    v2 = state_read_qword _ _ _ s1 src2 ->
    s3 = state_write_qword _ _ _ s2 dst (d v1 v2) ->
    s4 = run_effect_2 _ _ s3 f v1 v2 ->
    instr_step p k1 s1 (Some k2) s4

  | step_2_2 op dst1 dst2 src1 src2 k1 k2 s1 s2 s3 s4 s5 d f v1 v2 v1' v2' :
    instr _ _ _ k1 = instr_2_2 _ _ _ _ op dst1 dst2 src1 src2 k2 ->
    s2 = state_write_rip _ _ s1 (proj1_sig k2) ->
    Some d = computation_2_2 op ->
    Some f = effect_2_2 op ->
    v1 = state_read_qword _ _ _ s1 src1 ->
    v2 = state_read_qword _ _ _ s1 src2 ->
    v1' = fst (d v1 v2) ->
    v2' = snd (d v1 v2) ->
    s3 = state_write_qword _ _ _ s2 dst1 v1' ->
    s4 = state_write_qword _ _ _ s2 dst2 v2' ->
    s5 = run_effect_2 _ _ s5 f v1 v2 ->
    instr_step p k1 s1 (Some k2) s5

  | step_push (sp_s sp_d : Cell) src k1 k2 s1 s2 s3 s4 v sz :
    instr _ _ _ k1 = instr_push _ _ _ _ sp_s sp_d src k2 ->
    s2 = state_write_rip _ _ s1 (proj1_sig k2) ->
    v = state_read_qword _ _ _ s1 src ->
    s3 = state_write_qword _ _ _ s2 (dst_addr _ _ (sz, mk_addr_expr _ (Some sp_s) None scale1 _0)) v ->
    instr_step p k1 s1 (Some k2) s4

  | step_pop (sp_s sp_d : Cell) dst k1 k2 s1 s2 s3 s4 v sz :
    instr _ _ _ k1 = instr_pop _ _ _ _ dst sp_s sp_d k2 ->
    s2 = state_write_rip _ _ s1 (proj1_sig k2) ->
    v = state_read_qword _ _ _ s1 (src_addr _ _ (sz, mk_addr_expr _ (Some sp_s) None scale1 _0)) ->
    s3 = state_write_qword _ _ _ s2 dst v ->
    instr_step p k1 s1 (Some k2) s4

  | step_jmp src k1 k2 k_t s1 s2 :
    instr _ _ _ k1 = instr_jmp _ _ _ _ src k_t ->
    s2 = state_write_rip _ _ s1 (proj1_sig k2) ->
    In k2 k_t ->
    instr_step p k1 s1 (Some k2) s2

  | step_cjmp cond src k1 k2 k_t k_f s1 s2 c :
    instr _ _ _ k1 = instr_cjmp _ _ _ _ cond src k_t k_f ->
    s2 = state_write_rip _ _ s1 (proj1_sig k2) ->
    Some c = condition cond ->
    (c (state_flags _ _ s1) = true  -> In k2 k_t) ->
    (c (state_flags _ _ s1) = false -> k2 = k_f) ->
    instr_step p k1 s1 (Some k2) s2

  | step_call (sp_s sp_d : Cell) src k1 k2 kc kr s1 s2 s3 s4 v :
    instr _ _ _ k1 = instr_call _ _ _ _ sp_s sp_d src kc kr ->
    s2 = state_write_rip _ _ s1 (proj1_sig kr) ->
    v = state_read_qword _ _ _ s1 src ->
    label_value (proj1_sig k2) = v ->
    In k2 kc ->
    s3 = state_write_qword _ _ _ s2 (dst_addr _ _ (QWORD, mk_addr_expr _ (Some sp_s) None scale1 _0)) (label_value (proj1_sig kr)) ->
    instr_step p k1 s1 (Some k2) s4

  | step_ret (sp_s sp_d : Cell) k1 k2 s1 s2 v kr :
    instr _ _ _ k1 = instr_ret _ _ _ _ sp_s sp_d kr ->
    s2 = state_write_rip _ _ s1 (proj1_sig k2) ->
    In k2 kr ->
    v = state_read_qword _ _ _ s1 (src_addr _ _ (QWORD, mk_addr_expr _ (Some sp_s) None scale1 _0)) ->
    label_value (proj1_sig k2) = v ->
    instr_step p k1 s1 (Some k2) s2
    .

    Inductive step_star `{EqDec Label} `{IsCellState Cell Annot} `{IsLabel Label} (p : the_prog) :
      the_node p -> the_state -> option (the_node p) -> the_state -> Prop  :=

    | step_terminal s1 s2 k :
      instr_step p k s1 None s2 ->
      step_star  p k s1 None s2

    | step_nonterminal s1 s2 s3 s4 k1 k2 k3 k4 :
      instr_step p k1 s1 (Some k2) s2 ->
      phi_step   p k2 s2 k3 s3 ->
      step_star  p k3 s3 k4 s4 ->
      step_star  p k1 s1 k4 s4

      .

End SEMANTICS.
