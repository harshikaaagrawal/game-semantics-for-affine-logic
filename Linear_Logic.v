Require Import Coq.Program.Equality.
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Module Syntax1.
(* int x = 5 + 6 * 7 *)
(*       =
       /         \
    int x      5 + 6 * 7
     /  \           /   \
   int   x          5   6*7
                        /   \
                        6   7
*)
(* True /\ (True \/ False) -> True
     /                          \
True /\ (True \/ False)         True
   /                \           
   True          True \/ False
                    /    \
                   True    False
*)
(*            "->"
       /            \
    "/\"           "True"
/        \
"True"   "\/"
         /  \
    "True" "False"
*)
Inductive syntax := True | False 
 | And (Left : syntax) (Right : syntax)
 | Or (Left : syntax) (Right : syntax)
 | Implication (Left : syntax) (Right : syntax)
 | Negation (Right : syntax) 
 | Biconditional (Left : syntax) (Right : syntax).

Declare Scope syntax_scope.
Delimit Scope syntax_scope with syntax. (* allows writing foo%syntax to mean that foo is in syntax_scope *)
Bind Scope syntax_scope with syntax. (* means that functions taking variables of type syntax will
automatically parse those variables in syntax_scope *)
Notation "A /\ B" := (And A B) : syntax_scope.
Notation "A \/ B" := (Or A B) : syntax_scope.

Inductive provable : syntax -> Type :=
| Trivial : provable True
| And_intro Left Right (a : provable Left) (b : provable Right): provable (And Left Right)
| And_use_left Left Right (a : provable (And Left Right)) : provable Left
| And_use_right Left Right (a: provable (And Left Right)) : provable Right
| Or_intro_left Left Right (a : provable Left): provable (Or Left Right)
| Or_intro_right Left Right (a : provable Right): provable (Or Left Right)
(*
| Or_use Left Right P (a : provable Left -> provable P) (b : provable Right -> provable P)
      : (provable (Or Left Right) -> provable P)
*)
.

Lemma check1 : provable True.
Proof.
  apply Trivial.
Qed.

Lemma check2 : provable (True /\ True).
Proof.
  apply And_intro;
  apply Trivial.
Qed.

Lemma check3 : provable (True /\ True).
Proof.
  eapply And_use_left.
Abort.

Lemma check3 : forall A B, provable (A /\ B) -> provable (B /\ A).
Proof.
  intros A B H.
  assert (a : provable A).
  { eapply And_use_left.
    apply H. }
  assert (b : provable B).
  { eapply And_use_right.
    apply H. }
  apply And_intro.
  apply b.
  apply a.
Qed.

Lemma check4 : provable (True \/ False).
Proof.
  apply Or_intro_left.
  apply Trivial.
Qed.
  
Lemma check5 : provable (False \/ True).
Proof.
  apply Or_intro_right.
  apply Trivial.
Qed.

Lemma check6 : forall A B, provable (A \/ B) -> provable (B \/ A).
Proof.
  intros A B H.  
Abort.

Lemma consistent : provable False -> Logic.False.
Proof.
  intro proof.
  Locate False.
  dependent induction proof.
Abort.
End Syntax1.


Module Syntax2.
(* int x = 5 + 6 * 7 *)
(*       =
       /         \
    int x      5 + 6 * 7
     /  \           /   \
   int   x          5   6*7
                        /   \
                        6   7
*)
(* True /\ (True \/ False) -> True
     /                          \
True /\ (True \/ False)         True
   /                \           
   True          True \/ False
                    /    \
                   True    False
*)
(*            "->"
       /            \
    "/\"           "True"
/        \
"True"   "\/"
         /  \
    "True" "False"
*)
Inductive syntax := True | False 
 | And (Left : syntax) (Right : syntax)
 | Or (Left : syntax) (Right : syntax)
 | Implication (Left : syntax) (Right : syntax)
 | Negation (Right : syntax) 
 | Biconditional (Left : syntax) (Right : syntax).

Declare Scope syntax_scope.
Delimit Scope syntax_scope with syntax. (* allows writing foo%syntax to mean that foo is in syntax_scope *)
Bind Scope syntax_scope with syntax. (* means that functions taking variables of type syntax will
automatically parse those variables in syntax_scope *)
Notation "A /\ B" := (And A B) : syntax_scope.
Notation "A \/ B" := (Or A B) : syntax_scope.
Print Grammar constr.
Reserved Notation "Ctx |- A" (at level 100, no associativity).

(* ssreflect magic to use decidable membership *)
Lemma syntax_eqbP : Equality.axiom syntax_beq.
Proof.
  intros A B; pose proof (internal_syntax_dec_bl A B); pose proof (internal_syntax_dec_lb A B).
  destruct (syntax_beq A B); constructor.
  all: intuition congruence.
Qed.

Canonical syntax_eqMixin := EqMixin syntax_eqbP.
Canonical syntax_eqType := Eval hnf in EqType syntax syntax_eqMixin.

Inductive provable : seq syntax -> syntax -> Type :=
| Provable_in Ctx A
     (a : A \in Ctx)
(*------------------------------*)
:          Ctx |- A
 
(* either we can make these primitive rules, or we can set up the rules so that these two are provable *)
(* look at https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html for lemmas about seq *)
(*
| Shuffle Ctx1 Ctx2 A (a : Ctx1 |- A) (perm : perm_eq Ctx1 Ctx2) : Ctx2 |- A
| Weaken  Ctx1 Ctx2 A (a : Ctx1 |- A) (sub  : subseq  Ctx1 Ctx2) : Ctx2 |- A
*)
| Trivial Ctx

(*------------------------------*)
:         Ctx |- True

| And_intro Ctx Left Right
    (a : Ctx |- Left)      (b : Ctx |- Right)
(*--------------------------------------------------*)
:             Ctx |- Left /\ Right


| And_use Ctx1 Ctx2 Left Right P
      (a : Ctx1 ++ [:: Left  ; Right ] ++ Ctx2 |- P) (* Ctx1,Left,Right,Ctx2 |- P *)
(*--------------------------------------------------*)
:          Ctx1 ++ [:: Left /\ Right ] ++ Ctx2 |- P  (* Ctx1, Left/\Right, Ctx2 |- P *)

| And_intro_left Ctx Left Right
    (a : Ctx |- Left)      (b : Ctx |- Right)
(*--------------------------------------------------*)
:             Ctx |- Left \/ Right

where "Ctx |- A" := (provable Ctx%syntax A).
Locate "++".
(*
Left /\ Right |- Left
Left /\ Right |- Right

(Ctx |- Left /\ Right) -> (Ctx |- Left)
*)

| And_use_left Left Right (a : provable (And Left Right)) : provable Left
| And_use_right Left Right (a: provable (And Left Right)) : provable Right
| Or_intro_left Left Right (a : provable Left): provable (Or Left Right)
| Or_intro_right Left Right (a : provable Right): provable (Or Left Right)
(*
| Or_use Left Right P (a : provable Left -> provable P) (b : provable Right -> provable P)
      : (provable (Or Left Right) -> provable P)
*)
.

Lemma check1 : provable True.
Proof.
  apply Trivial.
Qed.

Lemma check2 : provable (True /\ True).
Proof.
  apply And_intro;
  apply Trivial.
Qed.

Lemma check3 : provable (True /\ True).
Proof.
  eapply And_use_left.
Abort.

Lemma check3 : forall A B, provable (A /\ B) -> provable (B /\ A).
Proof.
  intros A B H.
  assert (a : provable A).
  { eapply And_use_left.
    apply H. }
  assert (b : provable B).
  { eapply And_use_right.
    apply H. }
  apply And_intro.
  apply b.
  apply a.
Qed.

Lemma check4 : provable (True \/ False).
Proof.
  apply Or_intro_left.
  apply Trivial.
Qed.
  
Lemma check5 : provable (False \/ True).
Proof.
  apply Or_intro_right.
  apply Trivial.
Qed.

Lemma check6 : forall A B, provable (A \/ B) -> provable (B \/ A).
Proof.
  intros A B H.  
Abort.

Lemma consistent : provable False -> Logic.False.
Proof.
  intro proof.
  Locate False.
  dependent induction proof.
Qed.
End Syntax1.