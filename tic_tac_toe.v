Require Import Coq.Program.Equality.
Require Import Coq.btauto.Btauto.
Require Import Coq.Lists.Streams.
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Inductive player := player_1 | player_2 | empty.
Axiom later : forall {T}, T.
Definition row (board : seq (seq player)) : bool := later.

