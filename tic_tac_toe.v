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
Definition column (board : seq (seq player)) : bool := later.
Definition diagonal (board : seq (seq player)) : bool := later.
Definition output_board(board : seq (seq player)) : ___ := later.
Definition game_result(current_player : nat) (board : seq (seq player)) (moves_played : nat) : ___ := later.
Definition game_intro _____ : ____ := later.
