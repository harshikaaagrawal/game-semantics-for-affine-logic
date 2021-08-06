Require Import Coq.Program.Equality.
Require Import Coq.btauto.Btauto.
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
Notation "A -> B" := (Implication A B) : syntax_scope.
Notation "~ A" := (Negation A) : syntax_scope.
Notation "A <-> B" := (Biconditional A B) : syntax_scope.
Print Grammar constr.
Reserved Notation "Ctx ||- A" (at level 100, no associativity).

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
:          Ctx ||- A
 
(* either we can make these primitive rules, or we can set up the rules so that these two are provable *)
(* look at https://math-comp.github.io/htmldoc/mathcomp.ssreflect.seq.html for lemmas about seq *)
(*
| Shuffle Ctx1 Ctx2 A (a : Ctx1 ||- A) (perm : perm_eq Ctx1 Ctx2) : Ctx2 ||- A
| Weaken  Ctx1 Ctx2 A (a : Ctx1 ||- A) (sub  : subseq  Ctx1 Ctx2) : Ctx2 ||- A
*)
| Trivial Ctx

(*------------------------------*)
:         Ctx ||- True

| And_intro Ctx Left Right
    (a : Ctx ||- Left)      (b : Ctx ||- Right)
(*--------------------------------------------------*)
:             Ctx ||- Left /\ Right


| And_use Ctx1 Ctx2 Left Right P
      (a : Ctx1 ++ [:: Left  ; Right ] ++ Ctx2 ||- P) (* Ctx1,Left,Right,Ctx2 ||- P *)
(*--------------------------------------------------*)
:          Ctx1 ++ [:: Left /\ Right ] ++ Ctx2 ||- P  (* Ctx1, Left/\Right, Ctx2 ||- P *)

| Or_right_1 Ctx A B
      (a : Ctx ||- A)
(*--------------------------------------------------*)
:   Ctx ||- A \/ B

| Or_right_2 Ctx A B
      (b : Ctx ||- B)
(*--------------------------------------------------*)
:   Ctx ||- A \/ B

| Or_left Ctx1 Ctx2 A B P
    (a : Ctx1 ++ [:: A] ++ Ctx2 ||- P)       (b : Ctx1 ++ [:: B] ++ Ctx2 ||- P) 
(*--------------------------------------------------------------------------*)
: Ctx1 ++ [:: A \/ B] ++ Ctx2 ||- P
where "Ctx ||- A" := (provable Ctx%syntax A).
Locate "++".
(*
Left /\ Right ||- Left
Left /\ Right ||- Right

(Ctx ||- Left /\ Right) -> (Ctx ||- Left)
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

Lemma weaken_empty : forall Ctx A, ([:: ] ||- A) -> (Ctx ||- A).
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
    exfalso.
    clear -x.
    apply catss0 in x.
    destruct x as [a b].
    apply catss0 in b.
    destruct b as [c d].
    discriminate.
  }
  {
    apply Or_right_1.
    apply IHprovable.
    trivial.
  }
  { apply Or_right_2.
    apply IHprovable.
    trivial.
  }
  { exfalso.
    clear -x.
    apply catss0 in x.
    destruct x as [a b].
    apply catss0 in b.
    destruct b as [c d].
    discriminate.
  }
     
Qed.

Lemma check1 : [:: ] ||- True.
Proof.
  apply Trivial.
Qed.

Lemma check2 : [:: ] ||- True /\ True.
Proof.
  apply And_intro;
  apply Trivial.
Qed.

Lemma check3 : forall A B, [:: A /\ B ] ||- B /\ A.
Proof.
  intros A B.
  apply (And_use [::] [::] A B).
  simpl.
  apply And_intro.
  {
    apply Provable_in.
    Search (cons _ _) (_ \in _).
    rewrite in_cons.
    rewrite mem_head.
    Search (_ || true).
    apply orbT.
  }
  { apply Provable_in.
    rewrite mem_head.
    trivial.
  }
Qed.

Lemma check4 : [:: ] ||- True \/ False.
Proof.
  apply Or_right_1.
  apply Trivial.
Qed.
  
Lemma check5 : [::] ||- (False \/ True).
Proof.
  apply Or_right_2.
  apply Trivial.
Qed.

Lemma check6 : forall A B,[:: A \/ B] ||- (B \/ A).
Proof.
  intros A B.
  apply (Or_left [::] [::] A B).
  {
    simpl.
    apply Or_right_2.
    apply Provable_in.
    rewrite mem_head.
    trivial.
  }
  { simpl.
    apply Or_right_1.
    apply Provable_in.
    rewrite mem_head.
    trivial.
  }
Qed.  

(** Previously, we were copy-pasting
<<<
    exfalso.
    clear -x.
    apply catss0 in x.
    destruct x as [a b].
    apply catss0 in b.
    destruct b as [c d].
    discriminate.
>>>
to prove goals like
>>>
1 subgoal
Ctx1, Ctx2 : seq syntax
Left, Right : syntax
proof : Ctx1 ++ [:: Left; Right] ++ Ctx2 ||- False
IHproof : Ctx1 ++ [:: Left; Right] ++ Ctx2 = [::] ->
          False = False -> Logic.False
x : Ctx1 ++ [:: (Left /\ Right)%syntax] ++ Ctx2 = [::]
______________________________________(1/1)
Logic.False
>>>

Now we write a tactic to handle all goals which have a hypothesis which says that some concatenation of lists is empty.
*)
Ltac absurd_from_empty_cat :=
  repeat match goal with
         | [ H : _ ++ _ = [::] |- _ ] => apply catss0 in H
         | [ H : _ /\ _        |- _ ] => destruct H
         | [ H : _ :: _ = [::] |- _ ] => exfalso; discriminate
         end.

Lemma consistent : ([::] ||- False) -> Logic.False.
Proof.
  intro proof.
  dependent induction proof; try solve [ absurd_from_empty_cat ].
  {
    Search (_ \in [::]).
    rewrite in_nil in a.
    congruence.
  }
Qed.


Lemma consistent2 : ([:: True /\ True ] ||- False) -> Logic.False.
Proof.
  intro proof.
  dependent induction proof; try solve [ absurd_from_empty_cat ].
  {
    Search (_ \in [::]).
    Search (_ \in _ :: _).
    rewrite !in_cons in a.
    rewrite in_nil in a.
    simpl in a.
    congruence.
  }
  { assert (Ctx1 = [::]) by (destruct Ctx1 as [|? [|]]; simpl in *; congruence).
    simpl in *.
    subst; simpl in *.
    assert (Ctx2 = [::]) by (destruct Ctx2 as [|? [|]]; simpl in *; congruence).
    subst; simpl in *.
    assert (Left = True) by congruence.
    assert (Right = True) by congruence.
    subst.
Abort.

Print syntax.
Print "&&".
Fixpoint truth_value (x : syntax) : bool
  := match x with
     | True => true
     | False => false
     | And l r => truth_value l && truth_value r
     | Or l r => truth_value l || truth_value r
     | Implication l r => if truth_value l then truth_value r else true
     | Negation r => negb (truth_value r)
     | Biconditional l r => Bool.eqb (truth_value l) (truth_value r)
     end.
     
Compute truth_value (True).
Compute truth_value (True /\ False).
Compute truth_value (True -> False).
Compute truth_value (True <-> False).

Search "fold".
(* Fold (op) init list := accumulate list into init using op *)
Eval cbv [foldl] in foldl plus 0 [:: 1; 2; 3].
Compute foldl plus 10 [:: 2; 3; 4; 5].
Compute foldl max 0 [:: 1; 3; 0].
Compute foldl mult 1 [:: 1; 2; 3].
Compute foldl plus 0 [::].
Compute foldl mult 1 [::].
Definition truth_value_of_context (ctx : seq syntax) : bool
  := foldr andb true (map truth_value ctx).
  
Lemma truth_value_of_context_cons x ctx : truth_value_of_context (x :: ctx) = truth_value x && truth_value_of_context ctx.
Proof.
  reflexivity.
Qed.

Lemma foldr_cat_assoc A (s1 s2 : seq A) (init : A) (op : A -> A -> A)
  (init_idl : forall x, op init x = x) 
  (op_assoc : forall a b c, op a (op b c) = op (op a b) c)
: foldr op init (s1 ++ s2) = op (foldr op init s1) (foldr op init s2).
Proof.
  induction s1.
  {
    simpl.
    rewrite init_idl.
    reflexivity.
  }
  {
    simpl.
    rewrite IHs1.
    rewrite op_assoc.
    reflexivity.
  }
Qed.

Search "assoc" andb.

Lemma truth_value_of_context_cat Ctx1 Ctx2
: truth_value_of_context (Ctx1 ++ Ctx2) = truth_value_of_context Ctx1 && truth_value_of_context Ctx2.
Proof.
  unfold truth_value_of_context.
  Search map cat.
  rewrite map_cat.
  Search foldr cat.
  Search foldr.
  rewrite foldr_cat_assoc//.
  apply Bool.andb_assoc.
Qed.

Lemma truth_value_of_context_nil 
: truth_value_of_context [::] = true.
Proof.
  reflexivity.
Qed.

Theorem boolean_consistency : forall Ctx P, (Ctx ||- P) ->  truth_value_of_context Ctx = true -> truth_value P = true.
Proof.
  intros Ctx P H T.
  induction H.
  {
    induction Ctx.
    {
    
      Search (_ \in [::]).
      rewrite in_nil in a.
      congruence.
    }
    {
      Search (_ \in _ :: _).
      rewrite in_cons in a.
      rewrite truth_value_of_context_cons in T.
      revert a T.
      
      move => /orP [/eqP a|a] => /andP [T1 T2].
      {
        hnf in T1.
        subst a0.
        exact T1.
      }
      {
        info_auto.
      }
    }
  }
  
  { 
    simpl.
    reflexivity.
  }
  {
    simpl.
    rewrite IHprovable1 // IHprovable2 //.
  }
  {
    rewrite -> ?truth_value_of_context_cat in *.
    rewrite -> ?truth_value_of_context_cons in *.
    rewrite -> ?truth_value_of_context_nil in *.
    simpl in *.
    rewrite -> ?Bool.andb_assoc in *.
    Search (_ && true).
    rewrite -> ?Bool.andb_true_r in *.
    auto.
  }
  {
    simpl.
    rewrite IHprovable//. 
  }
  {
    simpl.
    rewrite IHprovable//.
    Search (_ || true).
    rewrite Bool.orb_true_r.
    reflexivity.
  }
  { 
    rewrite -> ?truth_value_of_context_cat in *.
    rewrite -> ?truth_value_of_context_cons in *.
    rewrite -> ?truth_value_of_context_nil in *.
    simpl in *.
    rewrite -> ?Bool.andb_true_iff in *.
    rewrite -> ?Bool.orb_true_iff in *.
    decompose [and or] T; auto.
  }
Qed.

Theorem boolean_consistency_converse : forall P Ctx, (Ctx ||- P) ->  truth_value_of_context Ctx = true -> truth_value P = true.
Proof.
        intros Ctx P H T.
        induction H.
End Syntax2.