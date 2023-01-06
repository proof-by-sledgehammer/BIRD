From BIRD Require Import Util Bits GenericSyntax GenericSemantics EarlyBirdSyntax.

(******************************************************************************)
(*** STATE                                                                    *)
(******************************************************************************)

Section STATE.

  Definition bird_vars := (bird_variable -> qword).

  Definition bird_variables_read_qword (vars : bird_vars) (v : bird_variable) : qword :=
    vars v.

  Definition bird_variables_read (vars : bird_vars) (v : bird_variable) (a : bird_variable_annot) : cell_word_type v a :=
    extract (bird_variables_read_qword vars v) (bird_var_pattern a).

  Definition bird_variables_write_qword (vars : bird_vars) (var : bird_variable) (v : qword) : bird_vars :=
    fun var' => if eqb var' var then v else bird_variables_read_qword vars var.

  Definition bird_variables_write (vars : bird_vars) (var : bird_variable) (a : bird_variable_annot) (v : cell_word_type var a) : bird_vars :=
    let old_val := bird_variables_read_qword vars var in
    bird_variables_write_qword vars var (insert old_val (bird_var_pattern a) v).

End STATE.

Instance bird_variables_IsCellState : IsCellState bird_variable bird_variable_annot :=
      { cells_read        := bird_variables_read
      ; cells_write       := bird_variables_write
      ; cells_read_qword  := bird_variables_read_qword
      ; cells_write_qword := bird_variables_write_qword
      }.

(******************************************************************************)
(*** NOTATION                                                                 *)
(******************************************************************************)

Notation bird_state := (state bird_variable bird_label).
