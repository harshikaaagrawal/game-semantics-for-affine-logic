Print nat.
Check O.
Check S O.
Check 3.
Check 30.
Check 30000.

Definition plus_one (n : nat) : nat := S n.
Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S m => m
  end.
Compute pred 5.
(*
Notation "( x ) = ( y )" := (eq x y) (format "'[hv' '[hv' ( '[hv ' x ']' ) ']' '//' = '//' '[hv' ( '[hv ' y ']' ) ']' ']'").
*)
Lemma pred_S : forall n : nat, pred (S n) = n.
Proof.
  cbv delta [pred]. cbv beta. cbv match. cbv beta.
  reflexivity.
Qed.
Lemma S_pred : forall n : nat, S (pred n) = n.
Proof.
  cbv delta [pred]. cbv beta.
  destruct n.
Abort.
Fixpoint add (x y : nat) : nat :=
  match y with
  | O => x
  | S y' (* y = S y', i.e., y' = y-1 *) => add (S x) y'
  end.
Compute add 3 4.
Compute add 2 5.
Compute add 10 13.
Infix "+" := add : nat_scope.
Notation "x '.+1'" := (S x) (format "x '.+1'", at level 9) : nat_scope.
(*Notation "( ( x )  + ( y ) )" := (add x y) : nat_scope.*)
Lemma add_S_r_alt : forall x y : nat, x + (S y) = S (x + y).
Proof.
  intros x y; revert x.
  pose y as CASE.
  induction y as [|y' IH].
  { cbn [add]. reflexivity. }
  { cbv zeta in IH.
    cbn [add] in *.
    intro n.
    specialize (IH (n.+1)).
    assumption. }
Qed.
(*
Lemma add_1_l : forall n, 1 + n = S n.
Proof.
  intro n.
  pose n as CASE.
  induction n as [|n' IH].
  { cbn [add]. reflexivity. }
  { cbv zeta in IH.
    cbn [add] in *.
*)
Lemma add_comm_0 : forall n : nat, n + 0 = 0 + n.
Proof.
  intro n.
  pose n as CASE.
  induction n as [|n' IH].
  { reflexivity. }
  { cbv zeta in IH.
    cbn [add] in IH.
    rewrite add_S_r_alt.
    cbn [add].
    congruence. Undo.
    rewrite <- IH. (* replace 0+n' with n' *)
    reflexivity. }
Qed.
Lemma add_comm_S : forall n m : nat, n + S m = S m + n.
Proof.
  intro n.
  pose n as CASE.
  induction n as [|n' IH].
  { intro m. rewrite add_S_r_alt.
    rewrite <- add_comm_0. (* cbn [add]. reflexivity. }
  { cbv zeta in IH.
    cbn [add] in IH.
    rewrite add_S_r_alt.
    cbn [add].
    congruence. Undo.
    rewrite <- IH. (* replace 0+n' with n' *)
    reflexivity. } *)
(* TODO Later *)
Abort.

Require Import ZArith QArith Lia PArith Znumtheory.
Local Open Scope Z_scope. Local Open Scope Q_scope.
Search (Z -> Q).
Coercion inject_Z : Z >-> Q.
Coercion Z.pos : positive >-> Z.
Local Open Scope Z_scope.
Lemma sqrt_two_irrational_helper_2 : forall x y : Z,
  x * x = 2 * y * y -> (2 | x).
Proof.
  intros x y Hxx2yy.
  assert (Hxxdiv : (2 | x * x)).
  Search Z.divide.
  { rewrite Hxx2yy, <- Z.mul_assoc.
    apply Z.divide_factor_l. }
  assert (two_prime : prime 2) by apply prime_2.
  apply prime_mult in Hxxdiv; [ | apply prime_2 ].
  destruct Hxxdiv; assumption.
Qed.
Lemma sqrt_two_irrational_helper : forall (x : Z) (y : positive),
  Z.gcd x y = 1 -> x * x = 2 * y * y -> False.
Proof.
  intros x y Hreduced.
  intro Hxx2yy.
  assert (Hx_even : (2 | x)) by now eapply sqrt_two_irrational_helper_2; eassumption.
  Print Z.divide.
  unfold Z.divide in Hx_even.
  destruct Hx_even as [z Hx_even].
  subst x.
  assert (Hyy2zz : y * y = 2 * z * z) by nia.
  assert (Hy_even : (2 | y)) by now eapply sqrt_two_irrational_helper_2; eassumption.
  unfold Z.divide in Hy_even.
  destruct Hy_even as [w Hy_even].
  symmetry in Hy_even; destruct Hy_even; clear y.
  clear -Hreduced.
  Search (Z.gcd (_ * _) (_ * _)).
  rewrite Z.gcd_mul_mono_r in Hreduced.
  cbn [Z.abs] in Hreduced.
  nia.
Qed.
Local Open Scope Q_scope.
Print Qred.
Search Z.ggcd.
(* TODO: make this work with Q *)
Theorem sqrt_two_irrational : forall q : Q, q * q = 2 -> False.
Proof.
  intro q.
  intro H.
  apply (f_equal Qred) in H.
  Search Qred Qmult.
  Search Qred.
Abort.
Close Scope Q_scope.

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Open Scope list_scope.
Coercion Z.to_nat : Z >-> nat.
Coercion Z.of_nat : nat >-> Z.
(*
Compute let a := 4 in let p := 3 in List.map (fun x : nat => a * x) (seq 1 (p - 1)).
*)
Theorem fermat_little : forall a p : Z, prime p -> ~(p | a) -> a^(p-1) mod p = 1 mod p.
Proof.
  intros a p p_prime p_not_divide_a.
  pose (multiples_of_a := List.map (fun x : nat => (a * x) mod p) (seq 1 (p - 1))).
  pose (permuted := List.map Z.of_nat (seq 1 (p - 1))).
  assert (H : Permutation multiples_of_a permuted).
  { 





