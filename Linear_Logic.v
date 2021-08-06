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
  
Theorem boolean_consistency : forall Ctx P, (Ctx ||- P) ->  truth_value_of_context Ctx = true -> truth_value P = true.
Proof.
     