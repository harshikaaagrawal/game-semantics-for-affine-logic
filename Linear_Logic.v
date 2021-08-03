Definition iffb (a b : bool) : bool
  := negb (xorb a b).

Notation "~ x" := (negb x) : bool_scope.
Infix "<->" := iffb : bool_scope.
Infix "->" := implb : bool_scope.

Lemma chapter_1_3_g : exists P Q,
(~(((~P) && (~Q)) <-> ~(P && (~Q))))%bool
  = true.
Proof.
  unshelve (do 2 econstructor);
    constructor.
Qed.
Print chapter_1_3_g.

(*
A := string
B := int
C := float

int string_to_int(string a); // f

float int_to_float(int b); // g

float string_to_float(string a) {
  return int_to_float(string_to_int(a));
}

*)

Definition compose {A B C}
  (f : A -> B) (g : B -> C)
 : A -> C
 := fun a : A => g (f a).

Section chapter_1_6.
Context (P Q R : Prop)
        (PQ : P <-> Q)
        (QR : Q <-> R).
Lemma chapter_1_6_a : Q <-> P.
Proof.
  destruct PQ as [P_Q Q_P].
  destruct QR as [Q_R R_Q].
  constructor.
  { exact Q_P. }
  { exact P_Q. }
Qed.

Lemma chapter_1_6_b : P <-> R.
Proof.
  destruct PQ as [P_Q Q_P].
  destruct QR as [Q_R R_Q].
  constructor.
  { exact (compose P_Q Q_R). }
  { exact (compose R_Q Q_P). }
Qed.

Lemma chapter_1_6_c: ~Q <-> ~P.
Proof.
  unfold "~".
  destruct PQ as [P_Q Q_P].
  constructor.
  { intro f.
    exact (compose P_Q f). }
  { intro g.
  exact (compose Q_P g). }
Qed.

Lemma chapter_1_6_d: P /\ Q <-> Q /\ R.
Proof.
  destruct PQ as [P_Q Q_P].
  destruct QR as [Q_R R_Q].
  constructor.
  { intro f.
    destruct f as [g h].
    constructor.
    { exact h. }
    { exact (Q_R h). }
  }
  { intro a.
  destruct a as [b c].
  constructor.
  { exact (Q_P b). }
{ exact b. }
}
Qed.

Lemma or_comm: P \/ Q <-> Q \/ P.
Proof.
  clear PQ QR.
  constructor.
  { intro f.
    destruct f as [f|f].
    { right. 
      exact f. }
    { left.
      exact f. }
  }
  {
  
  }
Qed.

Lemma chapter_1_6_e: P \/ Q <-> Q \/ R.
Proof.
  destruct PQ as [P_Q Q_P].
  destruct QR as [Q_R R_Q].
  constructor.
  { intro f.
    destruct f as [f|f].
    { right. 
      exact (f). }
    { }
  }
  {
  }
Qed.