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

Inductive player := player_1 | player_2.
Definition other_player (current_player : player) : player :=
match current_player with
|player_1 => player_2
|player_2 => player_1
end.

Definition pile := seq.
Definition set_cell (q : pile) (m : nat) (n : nat) (p : player) : pile :=
set_nth [::] q m n.

Definition make_move (q : pile) (current_player : player) (m : nat) (n : nat) : pile * bool := 
if (n <= nth x0 q m) then set_cell q m n current_player.

Definition game_result (current_player : player) : player :=
other_player current_player.





