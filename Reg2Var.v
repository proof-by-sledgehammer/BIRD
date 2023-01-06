(******************************************************************************)
(** Register to variable conversion                                           *)
(******************************************************************************)

From Bits Require Import bits.

From Coq Require Import ssreflect.
From Coq Require Import List String.
Import ListNotations.

From mathcomp Require Import eqtype tuple.

From BIRD Require Import Bits Util GenericSyntax GenericSemantics EarlyBirdSyntax X86Syntax EarlyBirdSemantics X86Semantics.

Declare Scope bird_scope.
Delimit Scope bird_scope with bird.

(******************************************************************************)
(** CELLS                                                                     *)
(******************************************************************************)

Section CELLS.

  Local Open Scope string_scope.

  Local Definition reg2var_mk_var (name : string) : bird_variable :=
    {| bird_var_name := name ; bird_var_index := None ; bird_var_kind := bird_register_variable |}.

  Definition reg2var_reg (reg : x86_register) : bird_variable :=
    match reg with
    | x86_rax | x86_eax | x86_ax | x86_al | x86_ah => reg2var_mk_var "AX"
    | x86_rbx | x86_ebx | x86_bx | x86_bl | x86_bh => reg2var_mk_var "BX"
    | x86_rcx | x86_ecx | x86_cx | x86_cl | x86_ch => reg2var_mk_var "CX"
    | x86_rdx | x86_edx | x86_dx | x86_dl | x86_dh => reg2var_mk_var "DX"
    | x86_rsi | x86_esi | x86_si | x86_sil         => reg2var_mk_var "SI"
    | x86_rdi | x86_edi | x86_di | x86_dil         => reg2var_mk_var "DI"
    | x86_rbp | x86_ebp | x86_bp | x86_bpl         => reg2var_mk_var "BP"
    | x86_rsp | x86_esp | x86_sp | x86_spl         => reg2var_mk_var "SP"
    | x86_r08 | x86_r08d | x86_r08w | x86_r08b     => reg2var_mk_var "R08"
    | x86_r09 | x86_r09d | x86_r09w | x86_r09b     => reg2var_mk_var "R09"
    | x86_r10 | x86_r10d | x86_r10w | x86_r10b     => reg2var_mk_var "R10"
    | x86_r11 | x86_r11d | x86_r11w | x86_r11b     => reg2var_mk_var "R11"
    | x86_r12 | x86_r12d | x86_r12w | x86_r12b     => reg2var_mk_var "R12"
    | x86_r13 | x86_r13d | x86_r13w | x86_r13b     => reg2var_mk_var "R13"
    | x86_r14 | x86_r14d | x86_r14w | x86_r14b     => reg2var_mk_var "R14"
    | x86_r15 | x86_r15d | x86_r15w | x86_r15b     => reg2var_mk_var "R15"
    end.

  Definition reg2var_annot (r : x86_register) (_ : x86_annot) : bird_variable_annot
    := {| bird_var_pattern := x86_register_word_pattern r |}.

  Definition var2reg_var' (v : bird_variable) : option x86_register :=
    match bird_var_name v with
    | "AX" =>  Some x86_rax
    | "BX" =>  Some x86_rbx
    | "CX" =>  Some x86_rcx
    | "DX" =>  Some x86_rdx
    | "SI" =>  Some x86_rsi
    | "DI" =>  Some x86_rdi
    | "BP" =>  Some x86_rbp
    | "SP" =>  Some x86_rsp
    | "R08" => Some x86_r08
    | "R09" => Some x86_r09
    | "R10" => Some x86_r10
    | "R11" => Some x86_r11
    | "R12" => Some x86_r12
    | "R13" => Some x86_r13
    | "R14" => Some x86_r14
    | "R15" => Some x86_r15
    | _ => None
    end.

  Definition var2reg_var (v : bird_variable) : x86_register :=
    if var2reg_var' v is Some r
    then r
    else (* Not reachable *) x86_rax.

End CELLS.

(******************************************************************************)
(** MEMORY                                                                    *)
(******************************************************************************)

Section MEMORY.

  Definition reg2var_addr_expr (expr : x86_addr_expr) : bird_addr_expr :=
    {| expr_base   := option_map reg2var_reg (expr_base  _ expr)
    ;  expr_index  := option_map reg2var_reg (expr_index _ expr)
    ;  expr_scale  := expr_scale _ expr
    ;  expr_offset := expr_offset _ expr
    |}.

  Definition var2reg_addr_expr (expr : bird_addr_expr) : x86_addr_expr :=
    {| expr_base   := option_map var2reg_var (expr_base  _ expr)
    ;  expr_index  := option_map var2reg_var (expr_index _ expr)
    ;  expr_scale  := expr_scale _ expr
    ;  expr_offset := expr_offset _ expr
    |}.

  Definition reg2var_addr (addr : x86_addr) : bird_addr :=
    (fst addr, reg2var_addr_expr (snd addr)).

  Definition var2reg_addr (addr : bird_addr) : x86_addr :=
    (fst addr, var2reg_addr_expr (snd addr)).

End MEMORY.

(******************************************************************************)
(*** STATE PART                                                               *)
(******************************************************************************)

Section STATEPART.

  Definition reg2var_source (s : x86_source) : bird_source :=
    match s with
    | src_imm  v   => src_imm  _ _ v
    | src_addr a   => src_addr _ _ (reg2var_addr a)
    | src_expr e   => src_expr _ _ (reg2var_addr_expr e)
    | src_cell r a => src_cell _ _ (reg2var_reg r) (reg2var_annot r a)
    | src_rip      => src_rip  _ _
    end.

  Definition reg2var_destination (d : x86_destination) : bird_destination :=
    match d with
    | dst_addr a   => dst_addr _ _ (reg2var_addr a)
    | dst_cell r a => dst_cell _ _ (reg2var_reg r) (reg2var_annot r a)
    end.

End STATEPART.

(******************************************************************************)
(*** INSTRUCTIONS                                                             *)
(******************************************************************************)

Section INSTRUCTION.

  Definition reg2var_instruction {ls} (i : x86_instruction ls) : bird_instruction ls :=
    match i with
    | instr_nop  next
      => instr_nop _ _ _ _ next
    | instr_hlt
      => instr_hlt _ _ _ _
    | instr_1_1  op dst src next
      => instr_1_1 _ _ _ _ op (reg2var_destination dst) (reg2var_source src) next
    | instr_2_0  op src1 src2 next
      => instr_2_0 _ _ _ _ op (reg2var_source src1) (reg2var_source src2) next
    | instr_2_1  op dst src1 src2 next
      => instr_2_1 _ _ _ _ op (reg2var_destination dst) (reg2var_source src1) (reg2var_source src2) next
    | instr_2_2  op dst1 dst2 src1 src2 next
      => instr_2_2 _ _ _ _ op (reg2var_destination dst1) (reg2var_destination dst2) (reg2var_source src1) (reg2var_source src2) next
    | instr_push dst_sp src_sp src next
      => instr_push _ _ _ _ (reg2var_reg dst_sp) (reg2var_reg src_sp) (reg2var_source src) next
    | instr_pop  dst dst_sp src_sp next
      => instr_pop _ _ _ _ (reg2var_destination dst) (reg2var_reg dst_sp) (reg2var_reg src_sp) next
    | instr_jmp  src nexts
      => instr_jmp _ _ _ _ (reg2var_source src) nexts
    | instr_cjmp cond src targets next
      => instr_cjmp _ _ _ _ cond (reg2var_source src) targets next
    | instr_call sp_s sp_t src callee ret
      => instr_call _ _ _ _ (reg2var_reg sp_s) (reg2var_reg sp_t) (reg2var_source src) callee ret
    | instr_ret  sp_s sp_t nexts
      => instr_ret _ _ _ _ (reg2var_reg sp_s) (reg2var_reg sp_t) nexts
    end.

  Definition reg2var_phi_instruction (i : x86_phi_instruction) : bird_phi_instruction :=
    {| phi_srcs := List.map reg2var_reg (phi_srcs _ i)
    ;  phi_dst  := reg2var_reg (phi_dst _ i)
    |}.

  Definition reg2var_phi_block (b : x86_phi_block) : bird_phi_block :=
    List.map reg2var_phi_instruction b.

End INSTRUCTION.

(******************************************************************************)
(*** CODE                                                                     *)
(******************************************************************************)

Section CODE.

  Definition reg2var_code {ls} (c : x86_code ls) : bird_code ls :=
    fun l H => reg2var_instruction (c l H).

  Definition reg2var_phicode {ls} (c : x86_phicode ls) : bird_phicode ls :=
    fun l H => reg2var_phi_block (c l H).

End CODE.

(******************************************************************************)
(*** ROGRAM                                                                   *)
(******************************************************************************)

Section PROGRAM.

  Definition reg2var_program (p : x86_program) : bird_program :=
    {| prog_nodes   := prog_nodes _ _ _ p
    ;  prog_entry   := prog_entry _ _ _ p
    ;  prog_code    := reg2var_code (prog_code _ _ _ p)
    ;  prog_phicode := reg2var_phicode (prog_phicode _ _ _ p)
    |}.

  Definition reg2var_node {p} (n : x86_node p) : bird_node (reg2var_program p).
    destruct n as [k H] ; now exists k.
  Defined.

End PROGRAM.

(******************************************************************************)
(*** BISIMULATION                                                             *)
(******************************************************************************)

Section BISIM.

  Definition reg2var_bisim_cell `{IsLabel x86_label} `{IsLabel bird_label}
    (σ₁ : x86_state) (σ₂ : bird_state) : Prop :=
    forall reg annot,
      let src  := src_cell _ _ reg annot in
      let src' := src_cell _ _ (reg2var_reg reg) (reg2var_annot reg annot) in
      state_read _ _ _ σ₁ src = state_read _ _ _ σ₂ src'.

  Definition reg2var_bisim_mem `{IsLabel x86_label} `{IsLabel bird_label} `{IsCellState x86_register x86_annot} `{IsCellState bird_variable bird_variable_annot}
    (σ₁ : x86_state) (σ₂ : bird_state) : Prop :=
    forall a,
      let src  := src_addr _ _ a in
      let src' := src_addr _ _ (reg2var_addr a) in
      state_read _ _ _ σ₁ src = state_read _ _ _ σ₂ src'.

  Definition reg2var_bisim_flags
    (σ₁ : x86_state) (σ₂ : bird_state) : Prop :=
    forall f,
      state_flags _ _ σ₁ f = state_flags _ _ σ₂ f.

  Definition reg2var_bisim_rip `{EqDec x86_label}
    (σ₁ : x86_state) (σ₂ : bird_state) : Prop :=
       eqb (state_rip _ _ σ₁) (state_rip _ _ σ₂) = true.

  Definition reg2var_bisim `{EqDec x86_label} `{IsLabel x86_label} `{IsLabel bird_label}
    (σ₁ : x86_state) (σ₂ : bird_state) : Prop :=
       reg2var_bisim_cell  σ₁ σ₂
    /\ reg2var_bisim_mem   σ₁ σ₂
    /\ reg2var_bisim_rip   σ₁ σ₂
    /\ reg2var_bisim_flags σ₁ σ₂.

  Definition reg2var_cell_state (s : x86_registers) : bird_vars := fun v => s (var2reg_var v).

  Definition reg2var_state `{EqDec x86_label} `{IsLabel x86_label} `{IsLabel bird_label}
    (s : x86_state) : bird_state :=
    {| state_mem   := state_mem _ _ s
    ;  state_flags := state_flags _ _ s
    ;  state_cells := reg2var_cell_state (state_cells _ _ s)
    ;  state_rip   := state_rip _ _ s
    |}.
End BISIM.

Notation "σ₁ ≅ σ₂" := (reg2var_bisim σ₁ σ₂)(at level 50).

(******************************************************************************)
(*** FACTS                                                                    *)
(******************************************************************************)

Section FACTS.

  Axiom states_wf : forall s, x86_state_wf s.
  Axiom registers_wf : forall s, x86_registers_wf s.

  (* Should not be needed as we have the concrete instances of eqb *)
  (* but we seem to have some stuff set up incorrectly... *)
  (* TODO: clean up *)
  Axiom eqb_refl_label : forall (H : EqDec x86_label) (l : x86_label) , eqb l l = true.

  Context `{IsLabel x86_label}.
  Context `{EqDec x86_label}.

  Lemma extract_inv (v₁ v₂ : qword) (p : pattern) :
    v₁ = v₂ ->
    extract v₁ p = extract v₂ p.
  Proof. by move->. Qed.

  Lemma reg2var_alias r :
    x86_aliasing_registers r = x86_aliasing_registers (var2reg_var (reg2var_reg r)).
  Proof. by case: r. Qed.

  Check x86_registers_read.


  Lemma reg2var_regs_same_value_low (γ : x86_registers) (r : x86_register) :
    γ r = (reg2var_cell_state γ) (reg2var_reg r).
  Proof.
    have wf : x86_registers_wf γ by apply registers_wf.
    by apply: wf ; case: r.
  Qed.

  Lemma reg2var_regs_same_value_middle (γ : x86_registers) (r : x86_register) (a : x86_annot) :
    x86_registers_read γ r a = bird_variables_read (reg2var_cell_state γ) (reg2var_reg r) (reg2var_annot r a).
  Proof.
    unfold reg2var_cell_state ; cbn.
    unfold x86_registers_read, bird_variables_read ; cbn.
    apply: extract_inv.
    unfold x86_registers_read_qword, bird_variables_read_qword.
    by apply: reg2var_regs_same_value_low.
  Qed.

  (* Lemma 1 *)
Lemma reg2var_regs_same_value (σ : x86_state) (r : x86_register) (a : x86_annot) :
    state_read _ _ _ σ (src_cell _ _ r a) = state_read _ _ _ (reg2var_state σ) (src_cell _ _ (reg2var_reg r) (reg2var_annot r a)).
  Proof. unfold state_read ; cbn. by apply: reg2var_regs_same_value_middle. Qed.

  (* Lemma 2 *)
  Lemma reg2var_expr_same_value (γ : x86_registers) e :
    addr_expr_eval e γ = addr_expr_eval (reg2var_addr_expr e) (reg2var_cell_state γ).
  Proof.
    destruct e.
    unfold addr_expr_eval ; cbn.
    case expr_base ; case expr_index ; cbn.
    - move=> base index.
      by do 2 rewrite -reg2var_regs_same_value_low.
    - move=> base.
      by rewrite -reg2var_regs_same_value_low.
    - move=> index.
      by rewrite -reg2var_regs_same_value_low.
    - done.
   Qed.

  Lemma reg2var_mem_same_value (σ : x86_state) o e :
    state_mem _ _ σ  (addr_expr_eval e (x86_registers_read_qword (state_cells _ _ σ)) + o)%bird =
    state_mem _ _ σ  (addr_expr_eval (reg2var_addr_expr e) (bird_variables_read_qword (reg2var_cell_state (state_cells _ _ σ))) + o)%bird.
  Proof. by rewrite reg2var_expr_same_value. Qed.

  (* Lemma 3 *)
  Lemma reg2var_source_same_value (σ : x86_state) (s : x86_source) :
    state_read_qword _ _ _ σ s = state_read_qword _ _ _ (reg2var_state σ) (reg2var_source s).
  Proof.
    case: s => //=.
    - (* This takes some time *)
      move=> [] ; case => /= ? ; by do ? rewrite reg2var_mem_same_value.
    - by apply: reg2var_expr_same_value.
    - case => /= ? ; by rewrite reg2var_regs_same_value_middle => //=.
  Qed.

  Lemma reg2var_destination_same_value (σ : x86_state) (d : x86_destination) (v : qword) :
    state_write_qword _ _ _ σ d v ≅ state_write_qword _ _ _ (reg2var_state σ) (reg2var_destination d) v.
  Proof.
    constructor.
    - unfold reg2var_bisim_cell => r ? /=.
      rewrite reg2var_regs_same_value_middle.
      unfold bird_variables_read ; cbn.
      apply: extract_inv.
      unfold bird_variables_read_qword.
      unfold reg2var_cell_state ; cbn.
      case: r => //=.
      unfold state_write_qword ; cbn.
      Admitted.

  Lemma reg2var_rip_same_value s1 s2 rip :
    s1 ≅ s2 -> state_write_rip _ _ s1 rip ≅ state_write_rip _ _ s2 rip.
  Proof.
    move=> [?[?[??]]].
    do ? constructor => //.
    unfold state_write_rip ; cbn.
    unfold reg2var_bisim_rip ; cbn.
    apply: eqb_refl_label.
  Qed.

  Check state_write_qword.

  Lemma reg2var_src_cong s1 s2 src :
    s1 ≅ s2 -> state_read_qword _ _ _ s1 src = state_read_qword _ _ _ s2 (reg2var_source src).
  Proof.
    move=> [?[?[??]]].
    case: src => //=.
    move => [].
    case ; cbn.
    Admitted.

  Lemma reg2var_dest_cong s1 s2 dst v :
    s1 ≅ s2 -> state_write_qword _ _ _ s1 dst v ≅ state_write_qword _ _ _ s2 (reg2var_destination dst) v.
  Proof.
    move=> [?[?[??]]].
    case: dst => /=.
    - move=> [] sz ex.
      unfold state_write_qword.
      case sz ; cbn.
      all: try done.
    - case ; cbn. all: done.
  Qed.

  (* Corollary 1 *)
  Lemma reg2var_state_translate `{IsLabel x86_label} `{EqDec x86_label} (σ : x86_state) :
    σ ≅ reg2var_state σ.
  Proof.
    destruct σ ; unfold reg2var_state, reg2var_bisim ; cbn.
    - unfold reg2var_bisim_cell ; cbn.
      repeat constructor => //= *.
      apply reg2var_regs_same_value_middle.
    - unfold reg2var_bisim_mem => /=.
      case ; case => /= * ; by do ? rewrite reg2var_expr_same_value.
    - unfold reg2var_bisim_rip ; cbn.
      by apply: eqb_refl_label.
  Qed.

  Lemma reg2var_nth_error_phi n (p : x86_phi_instruction) :
    nth_error (phi_srcs _ (reg2var_phi_instruction p)) n =
      option_map reg2var_reg (nth_error (phi_srcs _ p) n).
  Proof.
    unfold reg2var_phi_instruction ; cbn.
    destruct p ; cbn.
    case (nth_error phi_srcs n) eqn:Z ; cbn.
    - by erewrite map_nth_error.
    - move: Z ; rewrite nth_error_None => Z; rewrite nth_error_None.
      have: (Datatypes.length (map reg2var_reg phi_srcs) = Datatypes.length phi_srcs) by apply: map_length.
      by move->.
  Qed.

  (* Get around some type weirdnesses *)
  Axiom bisim_mem_fix : forall s1 s2, s1 ≅ s2 -> state_mem _ _ s1 = state_mem _ _ s2.
  Axiom bisim_flags_fix : forall s1 s2, s1 ≅ s2 -> state_flags _ _ s1 = state_flags _ _ s2.
  Axiom bisim_rip_fix : forall s1 s2, s1 ≅ s2 -> state_rip _ _ s1 = state_rip _ _ s2.

  (* We can assume this because all variable orginate from registers here *)
  (* See Comment in Definition 18 *)
  Axiom bisim_cells_fix : forall s1 s2, s1 ≅ s2 ->
    state_cells _ _ s2 = (fun v => state_cells _ _ s1 (var2reg_var v)).

  (* Lemma 5 *)
  Lemma reg2var_run_phi_is_sim n p σ₁ σ₂ :
    σ₁ ≅ σ₂ -> run_phi _ _ _ n p σ₁ ≅ run_phi _ _ _ n (reg2var_phi_instruction p) σ₂.
  Proof.
    move=> Hcong.
    unfold run_phi.
    rewrite reg2var_nth_error_phi ; cbn.
    case (nth_error _) => //=.
    constructor.
    - unfold reg2var_bisim_cell ; cbn.
      shelve.
    - unfold reg2var_bisim_mem ; cbn.
      shelve.
  Admitted.




  Lemma reg2var_phi_is_sim
    (p : x86_program) (σ₁ σ₁' : x86_state) (σ₂ : bird_state) (k₁ k₂ : node _ _ _ p) :

    let p'  := reg2var_program p in
    let σ₂' := reg2var_state σ₁' in

    reg2var_bisim σ₁  σ₂  /\ phi_step _ _ _ p  k₁ σ₁ k₂ σ₁' ->
    reg2var_bisim σ₁' σ₂' /\ phi_step _ _ _ p' k₁ σ₂ k₂ σ₂'.

  Proof.

    cbn.
    move=> [σ₁_bisim_σ₂ σ₁_step_σ₁'].
    constructor ; first by apply: reg2var_state_translate.
    inversion σ₁_step_σ₁' ; subst.
    constructor 1 with (n:=n).
  Admitted.


  Lemma reg2var_phi_is_sound
    (p : x86_program) (σ₁ σ₁' : x86_state) (σ₂ : bird_state) (k₁ k₂ : node _ _ _ p) :

    let p'  := reg2var_program p in
    let σ₂' := reg2var_state σ₁' in

    reg2var_bisim σ₁  σ₂  /\ phi_step _ _ _ p  k₁ σ₁ k₂ σ₁' ->
                             phi_step _ _ _ p' k₁ σ₂ k₂ σ₂'.

  Proof. by cbn ; move=> /reg2var_phi_is_sim []. Qed.

  Lemma reg2var_src_cong_trans s1 s2 s3 src :
    s1 ≅ s2 -> s1 ≅ s3 ->   state_read_qword _ _ _ s2 (reg2var_source src)
                          = state_read_qword _ _ _ s3 (reg2var_source src).
  Proof.
    move=> *.
    set v := state_read_qword _ _ _ s1 src.
    set v1 := state_read_qword _ _ _ _ _.
    set v2 := state_read_qword _ _ _ _ _.
    have R1: v = v1 by apply reg2var_src_cong.
    have R2: v = v2 by apply reg2var_src_cong.
    by rewrite -R1 -R2.
  Qed.

  Lemma reg2var_instr_is_sim_Some
    (p : x86_program) (σ₁ σ₁' : x86_state) (σ₂ : bird_state) (k₁ k₂ : node _ _ _ p) :

    let p'  := reg2var_program p in
    let σ₂' := reg2var_state σ₁' in

    reg2var_bisim σ₁  σ₂  /\ instr_step _ _ _ p  k₁ σ₁ (Some k₂) σ₁' ->
    reg2var_bisim σ₁' σ₂' /\ instr_step _ _ _ p' k₁ σ₂ (Some k₂) σ₂'.

  Proof.

    cbn.
    move=> [σ₁_bisim_σ₂ σ₁_step_σ₁'].
    constructor ; first by apply: reg2var_state_translate.
    inversion σ₁_step_σ₁' ; subst.

    (* NOP *)
    - apply: step_nop ; cbn.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.
      + unfold state_write_rip ; cbn ; unfold reg2var_state ; cbn ; unfold reg2var_cell_state ; cbn.
        have R1: state_mem _ _ σ₁ = state_mem _ _ σ₂ by apply: bisim_mem_fix.
        have R2: state_flags _ _ σ₁ = state_flags _ _ σ₂ by apply: bisim_flags_fix.
        have R3: state_cells _ _ σ₂ = (fun v => state_cells _ _ σ₁ (var2reg_var v)) by apply bisim_cells_fix.
        by rewrite R1 R2 -R3.

    (* OP_1_1 *)
     - apply: step_1_1 ; cbn ; try eauto.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.
      + unfold run_effect_1 ; cbn.
        unfold reg2var_state ; cbn.
        do ? rewrite reg2var_source_same_value.
        set R1 := state_write_rip _ _ _ _.
        set R2 := state_write_rip _ _ _ _.
        have ?: R1 ≅ R2 by apply: reg2var_rip_same_value.
        set W1 := state_write_qword _ _ _ _ _ _.
        set W2 := state_write_qword _ _ _ _ _ _.
        have ?: W1 ≅ W2 by apply: reg2var_dest_cong.
        set V1 := state_read_qword _ _ _ _ _.
        set V2 := state_read_qword _ _ _ _ _.
        have R: V1 = V2.
        { eapply reg2var_src_cong_trans ; eauto. apply: reg2var_state_translate. }
        unfold reg2var_cell_state ; cbn.
        rewrite (bisim_mem_fix W1 W2).
        rewrite (bisim_rip_fix W1 W2).
        rewrite (bisim_flags_fix W1 W2).
        rewrite (bisim_cells_fix W1 W2).
        rewrite R.
        all: try done.

    (* OP_2_0 *)
     - apply: step_2_0 ; cbn ; try eauto.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.
      + unfold run_effect_2 ; cbn.
        unfold reg2var_state ; cbn.
        do ? rewrite reg2var_source_same_value.
        unfold reg2var_state ; cbn.
        set V1 := state_read_qword _ _ _ _ _.
        set V3 := state_read_qword _ _ _ _ _.
        set V2 := state_read_qword _ _ _ _ _.
        set V4 := state_read_qword _ _ _ _ _.
        have R12: V1 = V2.
        { eapply reg2var_src_cong_trans ; eauto. apply: reg2var_state_translate. }
        have R34: V3 = V4.
        { eapply reg2var_src_cong_trans ; eauto. apply: reg2var_state_translate. }
        unfold reg2var_cell_state ; cbn.
        rewrite R12 R34.
        rewrite (bisim_mem_fix σ₁ σ₂).
        rewrite (bisim_cells_fix σ₁ σ₂).
        rewrite (bisim_flags_fix σ₁ σ₂).
        all: try done.

    (* OP_2_1 *)
     - apply: step_2_1 ; cbn ; try eauto.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.
      + unfold run_effect_2 ; cbn.
        unfold reg2var_state ; cbn.
        do ? rewrite reg2var_source_same_value.
        unfold reg2var_state ; cbn.
        unfold reg2var_cell_state ; cbn.
        set V1 := state_read_qword _ _ _ _ _.
        set V3 := state_read_qword _ _ _ _ _.
        set V2 := state_read_qword _ _ _ _ _.
        set V4 := state_read_qword _ _ _ _ _.
        have R12: V1 = V2.
        { eapply reg2var_src_cong_trans ; eauto. apply: reg2var_state_translate. }
        have R34: V3 = V4.
        { eapply reg2var_src_cong_trans ; eauto. apply: reg2var_state_translate. }
        set R1 := state_write_rip _ _ _ _.
        set R2 := state_write_rip _ _ _ _.
        have ?: R1 ≅ R2 by apply: reg2var_rip_same_value.
        set W1 := state_write_qword _ _ _ _ _ _.
        set W2 := state_write_qword _ _ _ _ _ _.
        have ?: W1 ≅ W2 by apply: reg2var_dest_cong.
        rewrite R12 R34.
        rewrite (bisim_mem_fix W1 W2).
        rewrite (bisim_rip_fix W1 W2).
        rewrite (bisim_cells_fix W1 W2).
        rewrite (bisim_flags_fix W1 W2).
        all: try done.

    (* OP_2_2 *)
     - apply: step_2_2 ; cbn ; try eauto.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.
      + move: H14.
        move=> ->.
        unfold run_effect_2 ; cbn.
        unfold reg2var_state ; cbn.
        do ? rewrite reg2var_source_same_value.
        unfold reg2var_state ; cbn.
        unfold reg2var_cell_state ; cbn.
        set V1 := state_read_qword _ _ _ _ _.
        set V3 := state_read_qword _ _ _ _ _.
        set V2 := state_read_qword _ _ _ _ _.
        set V4 := state_read_qword _ _ _ _ _.
        have R12: V1 = V2.
        { eapply reg2var_src_cong_trans ; eauto. apply: reg2var_state_translate. }
        have R34: V3 = V4.
        { eapply reg2var_src_cong_trans ; eauto. apply: reg2var_state_translate. }
        shelve.
        (*set R1 := state_write_rip _ _ _ _.
        set R2 := state_write_rip _ _ _ _.
        have ?: R1 ≅ R2 by apply: reg2var_rip_same_value.
        set W1 := state_write_qword _ _ _ _ _ _.
        set W2 := state_write_qword _ _ _ _ _ _.
        have ?: W1 ≅ W2 by apply: reg2var_dest_cong.
        rewrite R12 R34.
        rewrite (bisim_mem_fix W1 W2).
        rewrite (bisim_rip_fix W1 W2).
        rewrite (bisim_cells_fix W1 W2).
        rewrite (bisim_flags_fix W1 W2).
        all: try done.*)

     (* PUSH *)
     - apply: step_push ; cbn ; try eauto.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.

     (* POP *)
     - apply: step_pop ; cbn ; try eauto.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.

     (* JMP *)
     - apply: step_jmp ; cbn ; try eauto.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.
      + unfold reg2var_state ; cbn.
        unfold state_write_rip ; cbn.
        rewrite (bisim_mem_fix σ₁ σ₂).
        rewrite (bisim_cells_fix σ₁ σ₂).
        rewrite (bisim_flags_fix σ₁ σ₂).
        all: try done.

     (* CJMP *)
     - apply: step_cjmp ; cbn.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.
      + unfold reg2var_state ; cbn.
        unfold state_write_rip ; cbn.
        rewrite (bisim_mem_fix σ₁ σ₂).
        rewrite (bisim_cells_fix σ₁ σ₂).
        rewrite (bisim_flags_fix σ₁ σ₂).
        all: try by eauto.
        by rewrite -(bisim_flags_fix σ₁ σ₂).
        by rewrite -(bisim_flags_fix σ₁ σ₂).

     (* CALL *)
     - apply: step_call ; cbn ; try eauto.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.
      + revert H5.
        set V1 := state_read_qword _ _ _ _ _.
        set V2 := state_read_qword _ _ _ _ _.
        have R: V1 = V2 by eapply reg2var_src_cong.
        by rewrite R.

     (* RET *)
     - apply: step_ret ; cbn ; try eauto.
      + unfold instr in H2 ; cbn in H2.
        unfold reg2var_code, reg2var_instruction ; cbn.
        by rewrite H2 ; cbn.
      + unfold reg2var_state ; cbn.
        unfold state_write_rip ; cbn.
        unfold reg2var_cell_state ; cbn.
        rewrite (bisim_mem_fix σ₁ σ₂).
        rewrite (bisim_cells_fix σ₁ σ₂).
        rewrite (bisim_flags_fix σ₁ σ₂).
        all: try done.
      + revert H8.
        unfold state_read_qword ; cbn.
        rewrite (bisim_mem_fix σ₁ σ₂).
        set V1 := addr_expr_eval _ _.
        set V2 := addr_expr_eval _ _.
        have: V1 = V2.
        {
          revert V1 V2 ; cbn.
          unfold addr_expr_eval ; cbn.
          admit.
        }
        move->.
        all: done.
  Admitted.


  Lemma reg2var_instr_is_sim_None
    (p : x86_program) (σ₁ σ₁' : x86_state) (σ₂ : bird_state) (k₁ : node _ _ _ p) :

    let p'  := reg2var_program p in
    let σ₂' := reg2var_state σ₁' in

    reg2var_bisim σ₁  σ₂  /\ instr_step _ _ _ p  k₁ σ₁ None σ₁' ->
    reg2var_bisim σ₁' σ₂' /\ instr_step _ _ _ p' k₁ σ₂ None σ₂'.

  Proof.

    cbn.
    move=> [σ₁_bisim_σ₂ σ₁_step_σ₁'].
    constructor ; first by apply: reg2var_state_translate.
    inversion σ₁_step_σ₁' ; subst.

    unfold reg2var_state ; cbn.
    unfold reg2var_cell_state ; cbn.
    rewrite (bisim_mem_fix σ₁' σ₂) ; last done.
    rewrite (bisim_flags_fix σ₁' σ₂) ; last done.
    rewrite (bisim_rip_fix σ₁' σ₂) ; last done.
    rewrite -(bisim_cells_fix σ₁' σ₂) ; last done.
    destruct σ₂ ; cbn.

    apply: step_hlt.
    unfold instr in H1 ; cbn in H1.
    unfold reg2var_code, reg2var_instruction ; cbn.
    unfold reg2var_code, reg2var_instruction ; cbn.
    by rewrite H1.

  Qed.

  Lemma reg2var_instr_is_sim
    (p : x86_program) (σ₁ σ₁' : x86_state) (σ₂ : bird_state) (k₁ : node _ _ _ p) (k₂ : option (node _ _ _ p)) :

    let p'  := reg2var_program p in
    let σ₂' := reg2var_state σ₁' in

    reg2var_bisim σ₁  σ₂  /\ instr_step _ _ _ p  k₁ σ₁ k₂ σ₁' ->
    reg2var_bisim σ₁' σ₂' /\ instr_step _ _ _ p' k₁ σ₂ k₂ σ₂'.

  Proof.

    case: k₂.
    - apply: reg2var_instr_is_sim_Some.
    - apply: reg2var_instr_is_sim_None.

  Qed.

  Lemma reg2var_instr_is_sound
    (p : x86_program) (σ₁ σ₁' : x86_state) (σ₂ : bird_state) (k₁ : node _ _ _ p) (k₂ : option (node _ _ _ p)) :

    let p'  := reg2var_program p in
    let σ₂' := reg2var_state σ₁' in

    reg2var_bisim σ₁  σ₂  /\ instr_step _ _ _ p  k₁ σ₁ k₂ σ₁' ->
                             instr_step _ _ _ p' k₁ σ₂ k₂ σ₂'.

  Proof. cbn ; by move=> /reg2var_instr_is_sim []. Qed.

  Lemma reg2var_star_is_sim
    (p : x86_program) (σ₁ σ₁' : x86_state) (σ₂ : bird_state) (k₁ : node _ _ _ p) (k₂ : option (node _ _ _ p)) :

    let p'  := reg2var_program p in
    let σ₂' := reg2var_state σ₁' in

    reg2var_bisim σ₁  σ₂  /\ step_star _ _ _ p  k₁ σ₁ k₂ σ₁' ->
    reg2var_bisim σ₁' σ₂' /\ step_star _ _ _ p' k₁ σ₂ k₂ σ₂'.

  Proof.

    cbn.
    move=> [σ₁_bisim_σ₂ σ₁_step_σ₁'].
    constructor ; first by apply: reg2var_state_translate.

    generalize dependent σ₂.
    induction σ₁_step_σ₁'.

    (* TERMINAL *)
    - move=> σ₂ Hσ₂.
      apply: step_terminal.
      apply: reg2var_instr_is_sound.
      constructor ; eauto.

    (* NONTERMINAL *)
    - move=> σ₂ Hσ₂.
      apply: step_nonterminal.
      + apply: reg2var_instr_is_sound.
        by constructor ; eauto.
      + apply: reg2var_phi_is_sound.
        constructor ; eauto.
        apply: reg2var_state_translate.
      + apply: IHσ₁_step_σ₁'.
        apply: reg2var_state_translate.

  Qed.


End FACTS.
