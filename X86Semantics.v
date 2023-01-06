From Coq Require Import List.
Import ListNotations.

From BIRD Require Import Util Bits GenericSyntax GenericSemantics X86Syntax.

(******************************************************************************)
(*** ALIASING                                                                 *)
(******************************************************************************)

Section ALIAS.

  Definition x86_aliasing_registers (r : x86_register) : list x86_register :=
    match r with
    | x86_rax | x86_eax | x86_ax | x86_al | x86_ah => [x86_rax; x86_eax; x86_ax; x86_al; x86_ah]
    | x86_rbx | x86_ebx | x86_bx | x86_bl | x86_bh => [x86_rbx; x86_ebx; x86_bx; x86_bl; x86_bh]
    | x86_rcx | x86_ecx | x86_cx | x86_cl | x86_ch => [x86_rcx; x86_ecx; x86_cx; x86_cl; x86_ch]
    | x86_rdx | x86_edx | x86_dx | x86_dl | x86_dh => [x86_rdx; x86_edx; x86_dx; x86_dl; x86_dh]
    | x86_rsi | x86_esi | x86_si | x86_sil => [x86_rsi; x86_esi; x86_si; x86_sil]
    | x86_rdi | x86_edi | x86_di | x86_dil => [x86_rdi; x86_edi; x86_di; x86_dil]
    | x86_rbp | x86_ebp | x86_bp | x86_bpl => [x86_rbp; x86_ebp; x86_bp; x86_bpl]
    | x86_rsp | x86_esp | x86_sp | x86_spl => [x86_rsp; x86_esp; x86_sp; x86_spl]
    | x86_r08 | x86_r08d | x86_r08w | x86_r08b => [x86_r08; x86_r08d; x86_r08w; x86_r08b]
    | x86_r09 | x86_r09d | x86_r09w | x86_r09b => [x86_r09; x86_r09d; x86_r09w; x86_r09b]
    | x86_r10 | x86_r10d | x86_r10w | x86_r10b => [x86_r10; x86_r10d; x86_r10w; x86_r10b]
    | x86_r11 | x86_r11d | x86_r11w | x86_r11b => [x86_r11; x86_r11d; x86_r11w; x86_r11b]
    | x86_r12 | x86_r12d | x86_r12w | x86_r12b => [x86_r12; x86_r12d; x86_r12w; x86_r12b]
    | x86_r13 | x86_r13d | x86_r13w | x86_r13b => [x86_r13; x86_r13d; x86_r13w; x86_r13b]
    | x86_r14 | x86_r14d | x86_r14w | x86_r14b => [x86_r14; x86_r14d; x86_r14w; x86_r14b]
    | x86_r15 | x86_r15d | x86_r15w | x86_r15b => [x86_r15; x86_r15d; x86_r15w; x86_r15b]
    end.

  Definition x86_base_register (r : x86_register) : x86_register :=
    match r with
    | x86_rax | x86_eax | x86_ax | x86_al | x86_ah => x86_rax
    | x86_rbx | x86_ebx | x86_bx | x86_bl | x86_bh => x86_rbx
    | x86_rcx | x86_ecx | x86_cx | x86_cl | x86_ch => x86_rcx
    | x86_rdx | x86_edx | x86_dx | x86_dl | x86_dh => x86_rdx
    | x86_rsi | x86_esi | x86_si | x86_sil => x86_rsi
    | x86_rdi | x86_edi | x86_di | x86_dil => x86_rdi
    | x86_rbp | x86_ebp | x86_bp | x86_bpl => x86_rbp
    | x86_rsp | x86_esp | x86_sp | x86_spl => x86_rsp
    | x86_r08 | x86_r08d | x86_r08w | x86_r08b => x86_r08
    | x86_r09 | x86_r09d | x86_r09w | x86_r09b => x86_r09
    | x86_r10 | x86_r10d | x86_r10w | x86_r10b => x86_r10
    | x86_r11 | x86_r11d | x86_r11w | x86_r11b => x86_r11
    | x86_r12 | x86_r12d | x86_r12w | x86_r12b => x86_r12
    | x86_r13 | x86_r13d | x86_r13w | x86_r13b => x86_r13
    | x86_r14 | x86_r14d | x86_r14w | x86_r14b => x86_r14
    | x86_r15 | x86_r15d | x86_r15w | x86_r15b => x86_r15
    end.

End ALIAS.

(******************************************************************************)
(*** STATE                                                                    *)
(******************************************************************************)

Section STATE.

  Definition x86_registers := (x86_register -> qword).


  Definition x86_registers_read_qword (regs : x86_registers) (r : x86_register) : qword :=
    regs r.

  Definition x86_registers_read (regs : x86_registers) (r : x86_register) (a : x86_register_annot) : cell_word_type r a :=
    extract (x86_registers_read_qword regs r) (x86_register_word_pattern r).


  Definition x86_registers_write_qword_single (regs : x86_registers) (r : x86_register) (v : qword) : x86_registers :=
    fun r' => if eqb r r' then v else x86_registers_read_qword regs r'.

  Fixpoint x86_registers_write_qword_all (regs : x86_registers) (rs : list x86_register) (v : qword) : x86_registers :=
    match rs with
    | nil => regs
    | cur::rest =>
        x86_registers_write_qword_all (x86_registers_write_qword_single regs cur v) rest v
    end.

  Definition x86_registers_write_qword (regs : x86_registers) (r : x86_register) (v : qword) : x86_registers :=
    x86_registers_write_qword_all regs (x86_aliasing_registers r) v.

  Definition x86_registers_write (regs : x86_registers) (r : x86_register) (a : x86_register_annot) (v : cell_word_type r a) : x86_registers :=
    let old_val := x86_registers_read_qword regs r in
    x86_registers_write_qword regs r (insert old_val (x86_register_word_pattern r) v).

End STATE.

Instance x86_registers_IsCellState : IsCellState x86_register x86_register_annot :=
      { cells_read        := x86_registers_read
      ; cells_write       := x86_registers_write
      ; cells_read_qword  := x86_registers_read_qword
      ; cells_write_qword := x86_registers_write_qword
      }.

(******************************************************************************)
(*** NOTATION                                                                 *)
(******************************************************************************)

Notation x86_state := (state x86_register x86_label).

(******************************************************************************)
(*** WF                                                                       *)
(******************************************************************************)

Section WF.

  Definition x86_registers_wf (s : x86_registers) : Prop :=
    forall (r1 r2 : x86_register),
      x86_aliasing_registers r1 = x86_aliasing_registers r2 ->
      s r1 = s r2.

  Definition x86_state_wf (s : x86_state) : Prop :=
    forall (r1 r2 : x86_register), x86_registers_wf (state_cells _ _ s).

End WF.
