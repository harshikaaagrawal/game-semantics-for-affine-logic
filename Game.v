Require Import Coq.Program.Equality.
Require Import Coq.btauto.Btauto.
Require Import Coq.Lists.Streams.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
(*Require Import CoqProject.tic_tac_toe.*)
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype.
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype ssrnat.

Set Implicit Arguments.
Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Module tic_tac_toe.
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
Module Export structures.
Canonical player_eqMixin := EqMixin player_eqbP.
Canonical player_eqType := Eval hnf in EqType player player_eqMixin.
(*Canonical cell_eqMixin := EqMixin cell_eqbP.
Canonical cell_eqType := Eval hnf in EqType cell cell_eqMixin.*)
End structures.
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
Definition move_is_valid (b: board) (r : nat) (c : nat) : bool := 
(r <= 3) && (c <= 3) && (get_cell b r c == empty).
Definition make_move (b: board) (current_player : player) (r : nat) (c : nat) : board * bool := 
if move_is_valid b r c then(set_cell b r c current_player, true) else (b, false).
Definition make_single_move (state : board*player) (next_move : nat*nat) : (board*player)*bool :=
let (r, c) := next_move in
let (b, p) := state in 
let (new_board, is_valid) := make_move b p r c in 
((new_board, other_player p), is_valid).
Fixpoint make_moves (moves : seq (nat*nat)) (state : board*player) : board*player :=
match moves with
|[::] => state
|move :: moves => let new_state := fst (make_single_move state move) in
make_moves moves new_state
end.


Definition next_move_is_valid (moves_so_far : seq (nat * nat)) (next_move : nat * nat) : bool :=
let (r, c) := next_move in 
let (b, _) := make_moves moves_so_far initial_state in 
move_is_valid b r c.

Fixpoint game_outcome (moves : seq (nat * nat)) (state : board*player) : option player :=
(*None means game is still in progress, some player means game is over and that player won*)
match moves with 
| [::] => None 
| move :: moves => let (new_state, is_valid) := make_single_move state move in 
if is_valid 
  then match game_result new_state with 
       | None => game_outcome moves new_state
       | Some winner => Some winner
       end
  else
    Some (other_player (snd state)) 
end.

Compute output_board (fst (make_move initial_board player_1 1 2) ).
Compute output_board (fst (make_move (fst (make_move initial_board player_1 1 2)) player_2 1 1) ).
Compute output_board (fst (make_moves [:: (1, 1) ; (2, 2) ; (1, 0) ; (0,0) ; (1, 2)] initial_state)).
Compute game_result (make_moves [:: (1, 1) ; (2, 2) ; (1, 0) ; (0,0) ; (1, 2)] initial_state).
Search (seq _-> seq _-> bool).
End tic_tac_toe.
Export tic_tac_toe.structures.

Inductive player := player_O | player_P.
Lemma player_eqbP : Equality.axiom player_beq.
Proof. intros x y. pose proof (@internal_player_dec_bl x y); pose proof (@internal_player_dec_lb x y). 
  destruct player_beq ; constructor ; intuition congruence. Qed.
Module Export structures.
Canonical player_eqMixin := EqMixin player_eqbP.
Canonical player_eqType := Eval hnf in EqType player player_eqMixin.
End structures.
Definition other_player (p : player) : player
:= match p with
   | player_O => player_P
   | player_P => player_O
   end.

Module Streams.
Fixpoint firstn {A : Type} (s : Stream A) (n : nat) : seq A :=
match n with
| 0 => [::]
| S m => Streams.hd s :: firstn (Streams.tl s) m
end.
End Streams.

Module strict. 
Record game
:= { possible_move : Type
   ; first_player : player
   ; play_won_by_P : Stream possible_move -> Prop }.

Definition position (g : game) : Type
:= seq (possible_move g).

Search "even" (nat -> bool).
Definition next_player {g} (p : position g) : player
:= if Nat.even (List.length p) then first_player g else other_player (first_player g).

Definition strategy g (p : player) : Type
:= forall (pos : position g) (h : next_player pos = p), possible_move g.

End strict.

Module relaxed.
Record game
:= { possible_move : Type
   ; first_player : player
   ; play_won_by_P : Stream possible_move -> Prop
   ; next_player : seq possible_move -> player 
   ; next_move_is_valid : seq possible_move -> possible_move -> bool}.

Definition out_of_turn_move {g} (moves : seq (possible_move g)) (actual_current_player : player) : bool  :=  
actual_current_player != next_player g moves.
Definition first_invalid_move {g : game} (moves : seq (seq (possible_move g))) : option player :=
(* for(int i = 0; i <= ; i++)
   {
      for(int j = 0; j <= ; j++)
      {
          if(out_of_turn(moves[0 to i-1], i%2 ) || !next_move_is_valid(moves[0 to i], moves[i][j])
              return i%2

 *)
Definition to_strict (g : game) : strict.game.
refine {| strict.possible_move := seq (possible_move g)
   ; strict.first_player := first_player g
   
|}.

Definition player_follows_strategy {g} (p : player) (strat : strategy g p) (history : Stream (possible_move g)) : Prop. 
End relaxed.

Module tic_tac_toe_relaxed.
Definition tic_tac_toe_game : relaxed.game.
refine {| relaxed.possible_move := nat * nat
        ; relaxed.first_player := player_P
        ; relaxed.next_player moves_so_far := if Nat.even (List.length moves_so_far) then player_P else player_O
        ; relaxed.play_won_by_P all_moves := exists n : nat, tic_tac_toe.game_outcome (Streams.firstn all_moves n) tic_tac_toe.initial_state == Some tic_tac_toe.player_1
        ; relaxed.next_move_is_valid := tic_tac_toe.next_move_is_valid
        |}.

Defined.
End tic_tac_toe_relaxed.




