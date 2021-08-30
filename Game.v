Require Import Coq.Program.Equality.
Require Import Coq.btauto.Btauto.
Require Import Coq.Lists.Streams.
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Inductive player := player_O | player_P.
Definition other_player (p : player) : player
:= match p with
   | player_O => player_P
   | player_P => player_O
   end.

Record strict_game
:= { possible_move : Type
   ; first_player : player
   ; play_won_by_P : Stream possible_move -> Prop }.

Definition position (g : strict_game) : Type
:= seq (possible_move g).

Search "even" (nat -> bool).
Definition next_player {g} (p : position g) : player
:= if Nat.even (length p) then first_player g else other_player (first_player g).

Definition strategy g (p : player) : Type
:= forall (pos : position g) (h : next_player pos = p), possible_move g.

Definition player_follows_strategy {g} (p : player) (strat : strategy g p) (history : Stream (possible_move g)) : Prop.
:=


