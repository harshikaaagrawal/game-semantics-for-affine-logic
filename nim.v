Require Import Coq.Program.Equality.
Require Import Coq.btauto.Btauto.
Require Import Coq.Lists.Streams.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype ssrnat.

Set Implicit Arguments.
Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Notation new_line := (String "010" EmptyString) (only parsing).
Check new_line.

Axiom later : forall {T}, T.
Inductive player := player_1 | player_2.
Definition other_player (current_player : player) : player :=
match current_player with
|player_1 => player_2
|player_2 => player_1
end.

(*Definition pile := seq.*)
Definition set_cell_in_pile (q : seq nat) (index : nat) (n : nat) (p : player) : seq nat :=
(set_nth 0 q index n).

Definition game_result (current_player : player) : player :=
other_player current_player.

Definition play_game (q : seq nat) (current_player : player) : player := later. 
(*takes input, calls make_move*)
Definition game_state (q : seq nat) (current_player : player) : player := 
if q == [::] then game_result current_player else play_game q (other_player current_player). 

Definition make_move (q : seq nat) (current_player : player) (index : nat) (n : nat) : seq nat + player := 
if (n <= nth 0 q index) && (n != 0) then inl (set_cell_in_pile q index (nth 0 q index - n) current_player) && (game_state q current_player) else inr (game_result current_player).


