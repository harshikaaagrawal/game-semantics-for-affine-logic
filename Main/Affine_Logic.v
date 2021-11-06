Require Import Coq.Program.Equality.
Require Import Coq.btauto.Btauto.
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.


Module Syntax1.
Inductive syntax := Zero | One 
 | Tensor (Left : syntax) (Right : syntax)
 | With (Left : syntax) (Right : syntax)
 | Implication (Left : syntax) (Right : syntax)
 | Bang (Right : syntax).

Declare Scope syntax_scope.
Delimit Scope syntax_scope with syntax. (* allows writing foo%syntax to mean that foo is in syntax_scope *)
Bind Scope syntax_scope with syntax. (* means that functions taking variables of type syntax will
automatically parse those variables in syntax_scope *)
Print Grammar constr.
Notation "A * B" := (Tensor A B) : syntax_scope.
Notation "A && B" := (With A B) : syntax_scope.
Notation "A '-o' B" := (Implication A B) (at level 99) : syntax_scope.
Notation "! A" := (Bang A) (at level 9, format "! A") : syntax_scope.
Notation "0" := Zero : syntax_scope.
Notation "1" := One : syntax_scope.
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
| idA A

(*------------------------------*)
:          [:: A] ||- A


| permute_context Ctx1 Ctx2 P 

(a : perm_eq Ctx1 Ctx2)     (b : Ctx1 ||- P)
(*---------------------------------------------*)
:                  Ctx2 ||- P


| tensor_left Ctx A B P

    (a : A :: B :: Ctx ||- P)
(*------------------------------*)
:     A * B :: Ctx ||- P


| tensor_right Ctx1 Ctx2 A B
 (a : Ctx1 ||- A)    (b : Ctx2 ||- B)
(*------------------------------------*)
:     Ctx1 ++ Ctx2 ||- A * B



| with_left_1 Ctx A B P

      (a : A :: Ctx ||- P)
(*------------------------------*) 
:      A && B :: Ctx ||- P 

| with_left_2 Ctx A B P

      (a : B :: Ctx ||- P)
(*------------------------------*) 
:      A && B :: Ctx ||- P 


| with_right Ctx A B 

(a : Ctx ||- A)    (b : Ctx ||- B)
(*------------------------------*)
:       Ctx ||- A && B


| one_left Ctx P

          (a : Ctx ||- P)
(*------------------------------*)
:         1 :: Ctx ||- P


| one_right


(*------------------------------*)
:           [::] ||- 1


| zero_left Ctx P


(*------------------------------*)
:     0 :: Ctx ||- P


| implication_left Ctx1 Ctx2 A B P

      (a : Ctx1 ||- A)    (b : B :: Ctx2 ||- P)
(*--------------------------------------------------*)
:         (A -o B) :: Ctx1 ++ Ctx2 ||- P


| implication_right Ctx A B

     (a : A :: Ctx ||- B)
(*------------------------------*)
:      Ctx ||- (A -o B)

where "Ctx ||- A" := (provable Ctx%syntax A).

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

Fixpoint truth_value (x : syntax) : bool
  := match x with
     | One => true
     | Zero => false
     | Tensor l r => truth_value l && truth_value r
     | With l r => truth_value l && truth_value r
     | Implication l r => if truth_value l then truth_value r else true
     | Bang r => truth_value r
     end.
     
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

Search perm_eq.
Check catCA_perm_ind.

Lemma truth_value_of_context_perm Ctx1 Ctx2 : perm_eq Ctx1 Ctx2 -> truth_value_of_context Ctx1 = truth_value_of_context Ctx2.
Proof.
  Search perm_eq.
  Check catCA_perm_ind.
  intros A.
  pose proof (@catCA_perm_ind _ 
    (fun Ctx2 => truth_value_of_context Ctx1 = truth_value_of_context Ctx2)) as H.
  cbv beta in H.
  apply H with (s1 := Ctx1).
  {
    clear.
    intros s1 s2 s3 A.
    rewrite A.
    clear.
    rewrite !truth_value_of_context_cat.
    Search (?A && ?B = ?B && ?A).
    Search (_ && _ = _ && _).
    rewrite !Bool.andb_assoc.
    rewrite (Bool.andb_comm (truth_value_of_context s1) (truth_value_of_context s2)).
    reflexivity.
  }
  {
    exact A.
  }
  {
    reflexivity.
  }
Qed.

Theorem boolean_consistency : forall Ctx P, (Ctx ||- P) ->  truth_value_of_context Ctx = true -> truth_value P = true.
Proof.
  intros Ctx P H T.
  induction H;
  rewrite -> ?truth_value_of_context_cat, -> ?truth_value_of_context_cons, -> ?truth_value_of_context_nil, -> ?Bool.andb_true_r in *.
  all: simpl in *; auto.  
  all: rewrite -> ?truth_value_of_context_cat, -> ?truth_value_of_context_cons, -> ?truth_value_of_context_nil, -> ?Bool.andb_true_r in *.
  all: simpl in *; auto.  
  {
    apply truth_value_of_context_perm in a.
    rewrite -a // in T.
  }
  {
    rewrite -> ?Bool.andb_assoc in *.    
    assert (X : truth_value A = true) by auto.
    rewrite -> X in *.
    auto.
  }
  {
    rewrite T in IHprovable.
    Search (_ && true).
    rewrite -> Bool.andb_true_r in *.
    destruct (truth_value A); auto.
  }
Qed.

Inductive extended_nat := negative_infinity | positive_infinity | non_negative (_:nat).
Coercion non_negative : nat >-> extended_nat.
Declare Scope extended_nat_scope.
Delimit Scope extended_nat_scope with extended_nat.
Bind Scope extended_nat_scope with extended_nat.
Notation "-oo" := negative_infinity : extended_nat_scope.
Notation "+oo" := positive_infinity : extended_nat_scope.

Definition extended_plus (A B : extended_nat) : extended_nat
  := match A, B with 
     | -oo, -oo => -oo
     | -oo, non_negative _ => -oo
     | non_negative _, -oo => -oo
     | non_negative A, non_negative B => non_negative (A + B)
     end%extended_nat.
Infix "+" := extended_plus : extended_nat_scope.

Definition extended_minus (A B : extended_nat) : extended_nat
  := match A, B with 
     | -oo, -oo => -oo
     | -oo, non_negative _ => -oo
     | non_negative _, -oo => -oo
     | non_negative A, non_negative B => non_negative (A + B)
     end%extended_nat.
Infix "-" := extended_minus : extended_nat_scope.

Fixpoint resource_count (x : syntax) : extended_nat
  := match x with
     | One => 0
     | Zero => -oo
     | Tensor l r => resource_count l + resource_count r
     | With l _ =>  resource_count l
     | Implication l r => resource_count r - resource_count a
     | Bang r => truth_value r
     end%extended_nat.
     
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

Search perm_eq.
Check catCA_perm_ind.

Lemma truth_value_of_context_perm Ctx1 Ctx2 : perm_eq Ctx1 Ctx2 -> truth_value_of_context Ctx1 = truth_value_of_context Ctx2.
Proof.
  Search perm_eq.
  Check catCA_perm_ind.
  intros A.
  pose proof (@catCA_perm_ind _ 
    (fun Ctx2 => truth_value_of_context Ctx1 = truth_value_of_context Ctx2)) as H.
  cbv beta in H.
  apply H with (s1 := Ctx1).
  {
    clear.
    intros s1 s2 s3 A.
    rewrite A.
    clear.
    rewrite !truth_value_of_context_cat.
    Search (?A && ?B = ?B && ?A).
    Search (_ && _ = _ && _).
    rewrite !Bool.andb_assoc.
    rewrite (Bool.andb_comm (truth_value_of_context s1) (truth_value_of_context s2)).
    reflexivity.
  }
  {
    exact A.
  }
  {
    reflexivity.
  }
Qed.

Theorem boolean_consistency : forall Ctx P, (Ctx ||- P) ->  truth_value_of_context Ctx = true -> truth_value P = true.
Proof.
  intros Ctx P H T.
  induction H;
  rewrite -> ?truth_value_of_context_cat, -> ?truth_value_of_context_cons, -> ?truth_value_of_context_nil, -> ?Bool.andb_true_r in *.
  all: simpl in *; auto.  
  all: rewrite -> ?truth_value_of_context_cat, -> ?truth_value_of_context_cons, -> ?truth_value_of_context_nil, -> ?Bool.andb_true_r in *.
  all: simpl in *; auto.  
  {
    apply truth_value_of_context_perm in a.
    rewrite -a // in T.
  }
  {
    rewrite -> ?Bool.andb_assoc in *.    
    assert (X : truth_value A = true) by auto.
    rewrite -> X in *.
    auto.
  }
  {
    rewrite T in IHprovable.
    Search (_ && true).
    rewrite -> Bool.andb_true_r in *.
    destruct (truth_value A); auto.
  }
Qed.


