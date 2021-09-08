Require Import Coq.Program.Equality.
Require Import Coq.btauto.Btauto.
Require Import Coq.Lists.Streams.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype.

Set Implicit Arguments.
Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Notation new_line := (String "010" EmptyString) (only parsing).
Check new_line.


Inductive player := player_1 | player_2.
Axiom later : forall {T}, T.
Definition cell := option player.
Definition cell_to_string (c : cell) : string := 
match c with
|None => " "
|Some player_1 => "X"
|Some player_2 => "O"
end.
Definition board := seq (seq cell).
(*Scheme Equality for option. 
Notation cell_beq := (option_beq player_beq). *)

Lemma player_eqbP : Equality.axiom player_beq.
Proof. intros x y. pose proof (@internal_player_dec_bl x y); pose proof (@internal_player_dec_lb x y). 
  destruct player_beq ; constructor ; intuition congruence. Qed.
(*Notation internal_cell_dec_bl := (@internal_option_dec_bl _ _ (@internal_player_dec_bl)).
Notation internal_cell_dec_lb := (@internal_option_dec_lb _ _ (@internal_player_dec_lb)). *)
(*Lemma cell_eqbP : Equality.axiom cell_beq.
Proof. intros x y. pose proof (@internal_cell_dec_bl x y); pose proof (@internal_cell_dec_lb x y). 
  destruct cell_beq ; constructor ; intuition congruence. Qed.*)

Canonical player_eqMixin := EqMixin player_eqbP.
Canonical player_eqType := Eval hnf in EqType player player_eqMixin.
(*Canonical cell_eqMixin := EqMixin cell_eqbP.
Canonical cell_eqType := Eval hnf in EqType cell cell_eqMixin.*)
Definition empty : cell := None.
Coercion some_player (p : player) : cell := Some p.
Definition set_cell (b : board) (r : nat) (c : nat) (p : player) : board :=
set_nth [::] b r (set_nth empty (nth [::] b r) c p).
Definition get_cell (b : board) (r : nat) (c : nat) : cell := nth empty (nth [::] b r ) c.
Definition get_column (b : board) (c : nat) : seq cell :=
map (fun r => get_cell b r c) [:: 0 ; 1 ; 2 ].
Definition rows (b: board) : seq (seq cell) := b.
Search seq nat.
Definition columns (b : board) : seq (seq cell) := 
map (fun c => get_column b c) [:: 0 ; 1 ; 2 ].
Definition diagonals (b : board) : seq (seq cell) :=
[:: [:: get_cell b 0 0 ; get_cell b 1 1 ; get_cell b 2 2] ; [:: get_cell b 0 2 ; get_cell b 1 1 ; get_cell b 2 0] ].
Definition cells_same_non_empty (s : seq cell) : bool := foldr andb true (map (fun c => c == nth empty s 0) s)&& (nth empty s 0 != empty).
Definition any_cells_same_non_empty (s : seq (seq cell)) : bool := 
foldr orb false (map cells_same_non_empty s).
Definition any_row (b: board) : bool := 
any_cells_same_non_empty (rows b).
Definition any_column (b : board) : bool := 
any_cells_same_non_empty (columns b).
Definition any_diagonal (b : board) : bool :=
any_cells_same_non_empty (diagonals b).
Definition other_player (current_player : player) : player :=
match current_player with
|player_1 => player_2
|player_2 => player_1
end.
Compute nseq 3 empty.
Definition initial_board : board :=
nseq 3 (nseq 3 empty).
Locate "++". 
Definition output_row (s: seq cell) : string :=
foldr String.append ""%string (map cell_to_string s) ++ new_line.
Definition output_board (b : board) : string := 
foldr String.append ""%string (map output_row b).
Compute output_board initial_board.
Definition game_result (state : board * player) : option player := 
let (b, current_player) := state in
if any_row b || any_column b || any_diagonal b then Some (other_player current_player) else None.
Definition initial_state : board * player :=
(initial_board, player_1).
Definition game_result_string (p : option player) : string := later.
Definition game_intro : string := later.
Definition main_game (b : board) : unit := later.
Definition input_and_make_move (current_player : player) (b : board): player * board := later.
Definition make_move (b: board) (current_player : player) (r : nat) (c : nat) : board * bool := 
if (r <=? 3) && (c <=? 3) then (if get_cell b r c == empty then
 (set_cell b r c current_player, true) else (b, false))
 else (b, false).

Fixpoint make_moves (moves : seq (nat*nat)) (state : board*player) : board*player :=
match moves with
|[::] => state
|(r, c) :: moves => let new_state := (fst (make_move (fst state) (snd state) r c), other_player (snd state)) in
make_moves moves new_state
end.

Compute output_board (fst (make_move initial_board player_1 1 2) ).
Compute output_board (fst (make_move (fst (make_move initial_board player_1 1 2)) player_2 1 1) ).
Compute output_board (fst (make_moves [:: (1, 1) ; (2, 2) ; (1, 0) ; (0,0) ; (1, 2)] initial_state)).
Compute game_result (make_moves [:: (1, 1) ; (2, 2) ; (1, 0) ; (0,0) ; (1, 2)] initial_state).
Search (seq _-> seq _-> bool).