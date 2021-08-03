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

where "Ctx |- A" := (provable Ctx%syntax A).
Locate "++".
(*
Left /\ Right |- Left
Left /\ Right |- Right

(Ctx |- Left /\ Right) -> (Ctx |- Left)
*)
(*
| Or_intro_left Left Right (a : provable Left): provable (Or Left Right)
| Or_intro_right Left Right (a : provable Right): provable (Or Left Right)
*)
(*
| Or_use Left Right P (a : provable Left -> provable P) (b : provable Right -> provable P)
      : (provable (Or Left Right) -> provable P)
*)

Search ([::]) (_ ++ _).
Lemma catss0 : forall [T : Type] (s1 s2 : seq T),
  s1 ++ s2 = [::] -> s1 = [::] /\ s2 = [::].
Proof.
  destruct s1.
  {
    simpl.
    intros.
    split.
    {
      reflexivity.
    }
    {
      exact H.
    }
  }
  {
    simpl.
    intros.
    discriminate.
  }
Qed.

(* In C:
typedef struct Cell {
  void* hd;
  Cell* tl;
} Cell;
typedef Cell* seq;
// NULL is empty list, cell is non-empty list

// allocates a new list with head hd_value and tail tl_value
seq cons(void* hd_value, seq tl_value) {
  seq ret = (seq)malloc(sizeof(Cell));
  ret->hd = hd_value;
  ret->tl = tl_value;
  return ret;
}

// copies a list (values in the list are reused without being copied)
seq copy(seq s) {
}

// concatenates two sequences/lists
seq cat(seq s1, seq s2) {
  …
}
*)

Lemma weaken_empty : forall Ctx A, ([:: ] |- A) -> (Ctx |- A).
Proof.
  intros Ctx A H.
  dependent induction H.
  { (*variable branch*)
    (* an empty list has no elements, thus the statement is absurd*)
    Search (_ \in [::]).
    rewrite in_nil in a.
    congruence. }
  { apply Trivial.
  }
  { apply And_intro.
    { apply IHprovable1.
      reflexivity. }
    { apply IHprovable2.
      reflexivity.
      }
  }
  { (* And_use case *)
    (* absurd ctx1 with left right and  ctx2 are empty which is absurd *)
    (* x proves that there's a list with [Left /\ Right] in the middle of it which is also empty; this is absurd *)
    (* TODO: ask Rajee for help writing a comment that will remind future!Harshikaa how to do this case *)
    exfalso.
    clear -x.
    apply catss0 in x.
    destruct x as [a b].
    apply catss0 in b.
    destruct b as [c d].
    discriminate.
  }
    
Qed.

Lemma check1 : [:: ] |- True.
Proof.
  apply Trivial.
Qed.

Lemma check2 : [:: ] |- True /\ True.
Proof.
  apply And_intro;
  apply Trivial.
Qed.

Lemma check3 : forall A B, [:: A /\ B ] |- B /\ A.
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

Lemma check4 : [:: ] |- True \/ False.
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