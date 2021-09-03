Require Import Coq.Program.Equality.
Require Import Coq.btauto.Btauto.
Require Import Coq.Lists.Streams.
Require Import Coq.Strings.Strings.
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Inductive player := player_1 | player_2.
Axiom later : forall {T}, T.
Definition cell := option player.
Definition board := seq (seq cell).
Definition row (b: board) : bool := later.
Definition column (board : seq (seq player)) : bool := later.
Definition diagonal (board : seq (seq player)) : bool := later.
Definition output_board (board : seq (seq player)) : string := later.
Definition game_result (current_player : player) (board : seq (seq player)) (moves_played : nat) : option player := later.
Definition game_result_string (p : option player) : string := later.
Definition game_intro : string := later.
Definition main_game (board : seq (seq player)) : unit := later.
Definition input_and_make_move (current_player : player) (board : seq (seq player)): player*seq (seq player) := later.
Definition make_move (board : seq (seq player)) (current_player : player) (r : nat) (c : nat) : bool * seq (seq player) := later.
