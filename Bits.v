From Bits Require Import bits.

(******************************************************************************)
(*** Value                                                                    *)
(******************************************************************************)

Section VALUES.

  Local Open Scope type_scope.

  Definition bit   := bool.
  Definition byte  := BYTE.
  Definition word  := byte * byte.
  Definition dword := byte * byte * byte * byte.
  Definition qword := byte * byte * byte * byte * byte * byte * byte * byte.

  Definition qword_addc (a b : qword) : bit * qword :=
    let '(a1, a2, a3, a4, a5, a6, a7, a8) := a in
    let '(b1, b2, b3, b4, b5, b6, b7, b8) := b in
    let '(c8, v8) := adcB false a8 b8 in
    let '(c7, v7) := adcB c8    a7 b7 in
    let '(c6, v6) := adcB c7    a6 b6 in
    let '(c5, v5) := adcB c6    a5 b5 in
    let '(c4, v4) := adcB c5    a4 b4 in
    let '(c3, v3) := adcB c4    a3 b3 in
    let '(c2, v2) := adcB c3    a2 b2 in
    let '(c1, v1) := adcB c2    a1 b1 in
    (c1, (v1, v2, v3, v4, v5, v6, v7, v8)).

  Definition qword_add (a b : qword) : qword :=
    let '(_, v) := qword_addc a b in v.

  Definition qword_subb (a b : qword) : bit * qword :=
    let '(a1, a2, a3, a4, a5, a6, a7, a8) := a in
    let '(b1, b2, b3, b4, b5, b6, b7, b8) := b in
    let '(c8, v8) := sbbB false a8 b8 in
    let '(c7, v7) := sbbB c8    a7 b7 in
    let '(c6, v6) := sbbB c7    a6 b6 in
    let '(c5, v5) := sbbB c6    a5 b5 in
    let '(c4, v4) := sbbB c5    a4 b4 in
    let '(c3, v3) := sbbB c4    a3 b3 in
    let '(c2, v2) := sbbB c3    a2 b2 in
    let '(c1, v1) := sbbB c2    a1 b1 in
    (c1, (v1, v2, v3, v4, v5, v6, v7, v8)).

  Definition qword_sub (a b : qword) : qword :=
    let '(_, v) := qword_subb a b in v.

End VALUES.

Infix "+" := qword_add : bird_scope.

Section EXTRACTION_INSERTION.

  Variant pattern := full64 | low32 | low16 | low8 | high8.
  Variant word_size := BYTE | WORD | DWORD | QWORD.

  Definition word_type (s : word_size) :=
    match s with
    | BYTE => byte
    | WORD => word
    | DWORD => dword
    | QWORD => qword
    end.

  Definition pattern_word_size (p : pattern) :=
    match p with
    | full64        => QWORD
    | low32         => DWORD
    | low16         =>  WORD
    | low8 | high8  =>  BYTE
    end.

  Definition pattern_word_type (p : pattern) := word_type (pattern_word_size p).

  Let _0 : byte := #0.

  Definition extract_qword (v : qword) (p : pattern) : qword :=
    let '(v1, v2, v3, v4, v5, v6, v7, v8) := v in
    match p with
    | full64 => (v1, v2, v3, v4, v5, v6, v7, v8)
    | low32  => (_0, _0, _0, _0, v5, v6, v7, v8)
    | low16  => (_0, _0, _0, _0, _0, _0, v7, v8)
    | low8   => (_0, _0, _0, _0, _0, _0, _0, v8)
    | high8  => (_0, _0, _0, _0, _0, _0, v7, _0)
    end.

  Definition insert_qword (v : qword) (p : pattern) (b : qword) : qword :=
    let '(v1, v2, v3, v4, v5, v6, v7, v8) := v in
    let '(b1, b2, b3, b4, b5, b6, b7, b8) := b in
    match p with
    | full64 => (b1, b2, b3, b4, b5, b6, b7, b8)
    | low32  => (_0, _0, _0, _0, b5, b6, b7, b8)
    | low16  => (v1, v2, v3, v4, v5, v6, b7, b8)
    | low8   => (v1, v2, v3, v4, v5, v6, v7, b8)
    | high8  => (v1, v2, v3, v4, v5, v6, b7, v8)
    end.

  Definition extract (v : qword) (p : pattern) : pattern_word_type p :=
    let '(v1, v2, v3, v4, v5, v6, v7, v8) := v in
    match p return pattern_word_type p with
    | full64 => (v1, v2, v3, v4, v5, v6, v7, v8)
    | low32  => (                v5, v6, v7, v8)
    | low16  => (                        v7, v8)
    | low8   => (                            v8)
    | high8  => (                        v7    )
    end.

  Definition insert (v : qword) (p : pattern) (b : pattern_word_type p) : qword :=
    let w := pattern_word_type in
    let '(v1, v2, v3, v4, v5, v6, v7, v8) := v in
    match p as p' return w p = w p' -> w p' -> qword with
    | full64 => fun _ b' =>
                  let '(b1, b2, b3, b4, b5, b6, b7, b8) := b' in
                  (b1, b2, b3, b4, b5, b6, b7, b8)
    | low32  => fun _ b' =>
                  let '(                b5, b6, b7, b8) := b' in
                  (_0, _0, _0, _0, b5, b6, b7, b8)
    | low16  => fun _ b' =>
                  let '(                        b7, b8) := b' in
                  (v1, v2, v3, v4, v5, v6, b7, b8)
    | low8   => fun _ b' =>
                  let                               b8  := b' in
                  (v1, v2, v3, v4, v5, v6, v7, b8)
    | high8  => fun _ b' =>
                  let                            b7     := b' in
                  (v1, v2, v3, v4, v5, v6, b7, v8)
    end eq_refl b.

End EXTRACTION_INSERTION.
