Require Import Coq.Program.Equality.
Require Import Coq.btauto.Btauto.
Require Import Coq.Lists.Streams.
Require Import Coq.Strings.Strings.
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Inductive player := player_1 | player_2 | empty.
Axiom later : forall {T}, T.
Definition row (board : seq (seq player)) : bool := later.
Definition column (board : seq (seq player)) : bool := later.
Definition diagonal (board : seq (seq player)) : bool := later.
Definition output_board (board : seq (seq player)) : string := later.
Definition game_result (current_player : nat) (board : seq (seq player)) (moves_played : nat) : player := later.
Definition game_result_string (p : player) : string := later.
Definition game_intro : string := later.
