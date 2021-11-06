Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
Require Import Coq.btauto.Btauto.
Require Import Coq.Lists.Streams.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.Arith.
(*Require Import CoqProject.tic_tac_toe.*)
From Coq.ssr Require Import ssreflect ssrfun ssrbool.
From mathcomp.ssreflect Require Import seq eqtype ssrnat.

Set Implicit Arguments.
Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Axiom later : forall {T}, T.

(*
Transparent some_nat.
Opaque some_nat.
Definition some_nat : nat.
exact 42.
Defined.
Definition some_other_nat : nat.
exact 42.
Qed.
Lemma equal_nats : some_nat = some_other_nat.
Proof.
  unfold some_nat.
  unfold some_other_nat.
Abort.
*)


Print iota. 
Module Export List.
Definition enumerate {A} (s : seq A) : seq (nat*A) := 
zip (iota 0 (size s)) s.
Lemma enumerate_rcons {A} (s : seq A) (v : A)
: enumerate (rcons s v) = rcons (enumerate s) (size s, v).
Proof.
  change (size s) with (0 + size s).
  unfold enumerate.
  generalize 0.
  rewrite size_rcons.
  induction s as [|s1 ss IHs].
  { simpl.
    intro n.
    rewrite (_ : n + 0 = n) //.
    rewrite -plusE. lia. }
  { simpl.
    intro n.
    specialize (IHs n.+1).
    simpl in IHs.
    rewrite IHs.
    rewrite (_ : n + (size ss).+1 = n.+1 + size ss) //.
    rewrite -plusE. lia.
  }
Qed.
(* flatten_rcons *)
Section partition_map.
  Context {A B C}
          (f : A -> B + C).
  Fixpoint partition_map (ls  : seq A) : seq B * seq C :=
    match ls with
    | [::] => ([::], [::])
    | x :: xs => let (bs, cs) := partition_map xs in
                 match f x with
                 | inl b => (b :: bs, cs)
                 | inr c => (bs, c :: cs)
                 end
    end.
End partition_map.
End List.
Module tic_tac_toe.
Notation new_line := (String "010" EmptyString) (only parsing).
Check new_line.

Inductive player := player_1 | player_2.
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

Definition next_move_is_valid_or_game_finished (moves_so_far : seq (nat * nat)) (next_move : nat * nat) : bool :=
next_move_is_valid moves_so_far next_move || (game_outcome moves_so_far initial_state != None).

End tic_tac_toe.
Export tic_tac_toe.structures.

Section Logic.
Lemma forall_iff_compat {T} {P Q : T -> Prop}
: (forall x, P x <-> Q x) -> ((forall x, P x) <-> (forall y, Q y)).
Proof. firstorder. Qed.
End Logic.

Inductive player := player_O | player_P.
Declare Scope player_scope.
Delimit Scope player_scope with player.
Bind Scope player_scope with player.
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

Notation "~ p" := (other_player p) : player_scope.

Module Streams.
Fixpoint firstn {A : Type} (s : Stream A) (n : nat) : seq A :=
match n with
| 0 => [::]
| S m => Streams.hd s :: firstn (Streams.tl s) m
end.


Fixpoint nth {A : Type} (s : Stream A) (n : nat) : A := 
match n with
| 0 => Streams.hd s
| S m => nth (Streams.tl s) m
end.
CoFixpoint count_up_from (n : nat) : Stream nat := Streams.Cons n (count_up_from (n.+1)).
(** We need to flip the arguments to appease Coq's guard checker :-/ *)
Section prepend_helper.
  Context {A : Type} (s : Stream A).
  CoFixpoint prepend_helper (ls : seq A) : Stream A
    := match ls with
       | [::] => s
       | x :: xs => Streams.Cons x (prepend_helper xs)
       end.
End prepend_helper.
Definition prepend {A} (ls : seq A) (s : Stream A) : Stream A
  := prepend_helper s ls.
CoFixpoint flatten {A} (s : Stream (A * list A)) : Stream A
  := let (x, xs) := Streams.hd s in Streams.Cons x (prepend xs (flatten (Streams.tl s))).
Axiom extensionality : forall {A} (s1 s2 : Stream A), Streams.EqSt s1 s2 -> s1 = s2.
Print Streams.EqSt.  
Lemma firstn_succ {A} (s : Stream A) (n : nat) : firstn s (n.+1) = rcons (firstn s n) (nth s n).
Proof.
  revert s; induction n as [|n IHn]; intro s.
  { simpl.
    reflexivity.
  } 
  {
    simpl in *.
    apply f_equal.
    apply IHn.
  }
Qed.
End Streams.

Declare Scope game_scope.
Delimit Scope game_scope with game.
Declare Scope strategy_scope.
Delimit Scope strategy_scope with strategy.
Module strict. 
Record game
:= { possible_move : Type
   ; first_player : player
   ; play_won_by_P : Stream possible_move -> Prop
   ; play_won_by_O : Stream possible_move -> Prop
   ; no_duplicate_winner : forall all_moves, play_won_by_P all_moves -> play_won_by_O all_moves -> False
   (* same as
      forall all_moves, play_won_by_P all_moves -> (play_won_by_O all_moves -> False)
      roughly the same as
      forall all_moves, (play_won_by_P all_moves /\ play_won_by_O all_moves) -> False *)
    }.
Module Export game_binding.   
Bind Scope game_scope with game.
End game_binding.

Definition position (g : game) : Type
:= seq (possible_move g).

Definition play (g : game) : Type
:= Stream (possible_move g).

Definition next_player {g} (p : position g) : player
:= if Nat.even (List.length p) then first_player g else other_player (first_player g).

Definition strategy g (p : player) : Type
:= forall (pos : position g) (*(h : next_player pos == p)*), possible_move g.

Module Export strategy_binding.
Bind Scope strategy_scope with strategy.
End strategy_binding.

Definition player_follows_strategy {g} (p : player) (s : strategy g p) (all_moves : play g) : Prop := 
forall n : nat, let initial_segment := Streams.firstn all_moves n in 
forall h : next_player initial_segment == p, 
Streams.nth all_moves (n.+1) = s initial_segment.

(* make [p] not implicit *)
Global Arguments player_follows_strategy {g} p s all_moves.

Definition play_won_by {g} (p : player) (all_moves : play g) : Prop :=
match p with
| player_P => play_won_by_P g all_moves
| player_O => play_won_by_O g all_moves
end.

Definition winning_strategy {g} {p : player} (s : strategy g p) : Prop :=
forall all_moves : play g, player_follows_strategy p s all_moves -> play_won_by p all_moves. 

Definition determined (g : game) : Type := { s : strategy g player_P | winning_strategy s } + { s : strategy g player_O | winning_strategy s }.
(* If any winning strategy for P can be transformed into a winning strategy for O and also vice versa, then the game is not determined*) 

Definition negation (g : game) : game.
refine {| possible_move := possible_move g
        ; first_player := other_player (first_player g)
        ; play_won_by_P all_moves := play_won_by_O g all_moves 
        ; play_won_by_O all_moves := play_won_by_P g all_moves
        ; no_duplicate_winner all_moves P_winner O_winner := no_duplicate_winner g all_moves O_winner P_winner |}.
Defined.
Notation "~ g" := (negation g) : game_scope.

Definition negation_strategy {g} {p} (s : strategy g p) : strategy (~g) (~p) := s.

Notation "~ s" := (negation_strategy s) : strategy_scope.

Lemma negation_player_follows_strategy {g} {p} {s : strategy g p} {all_moves : play g} 
: player_follows_strategy p s all_moves <-> player_follows_strategy (~p) (~s) all_moves.
Proof.
  unfold player_follows_strategy.
  apply forall_iff_compat.
  intro n.
  apply imp_iff_compat_r.
  unfold next_player.
  simpl.
  generalize (Nat.even (Datatypes.length (Streams.firstn all_moves n))); intro fp_move.
  generalize (first_player g); intro fp.
  Local Open Scope player_scope.
  destruct fp_move, fp, p.
  all: simpl.
  all: done.
Qed.
Lemma negation_play_won_by {g} {p} {all_moves : play g}
 : play_won_by p all_moves <-> play_won_by (g:=~g) (~ p) all_moves.
Proof.
  unfold play_won_by in *.
  simpl.
  destruct p.
  { simpl.
    reflexivity.
  }
  { simpl.
    reflexivity.
  }
Qed.
Lemma negation_winning_strategy {g} {p} {s : strategy g p} : winning_strategy s <-> winning_strategy (~s).
Proof.
  unfold winning_strategy.
  unfold winning_strategy.
  apply forall_iff_compat; intro w.
  rewrite <- negation_player_follows_strategy.
  apply imp_iff_compat_l.
  apply negation_play_won_by.
Qed.  

Definition top : game.
refine {| possible_move := unit 
        ; first_player := player_P
        ; play_won_by_P all_moves := True
        ; play_won_by_O all_moves := False 
        ; no_duplicate_winner all_moves P_wins O_wins := O_wins    
|}.
Defined.

Definition trivial_strategy {p} : strategy top p := fun all_moves_so_far => tt.
CoFixpoint trivial_play : play top := Streams.Cons tt trivial_play.
Lemma top_player_follows_strategy {p} {s : strategy top p} {all_moves : play top} 
: player_follows_strategy p s all_moves.
Proof.
  unfold player_follows_strategy.
  intros n Hp.
  destruct (Streams.nth all_moves n.+1).
  destruct (s (Streams.firstn all_moves n)).
  reflexivity.
Qed.
Lemma top_play_won_by {p} {all_moves : play top}
 : play_won_by p all_moves <-> p = player_P.
Proof.
  unfold play_won_by, play_won_by_P, play_won_by_O, top.
  case: p => //.
Qed.
Lemma top_winning_strategy {p} {s : strategy top p}
 : winning_strategy s <-> p = player_P.
Proof.
  unfold winning_strategy.
  setoid_rewrite top_play_won_by.
  firstorder.
  eapply H.
  apply top_player_follows_strategy.
  Unshelve.
  exact trivial_play.
Qed. 

Definition bottom : game.
refine {| possible_move := unit
        ; first_player := player_O
        ; play_won_by_P all_moves := False
        ; play_won_by_O all_moves := True
        ; no_duplicate_winner all_moves P_wins O_wins := P_wins
|}.
Defined.

Lemma bottom_player_follows_strategy {p} {s : strategy bottom p} {all_moves : play bottom}
: player_follows_strategy p s all_moves.
Proof.
unfold player_follows_strategy.
intros n Hp.
destruct (Streams.nth all_moves n.+1).
destruct (s (Streams.firstn all_moves n)).
reflexivity.
Qed.

Lemma bottom_play_won_by {p} {all_moves : play bottom}
: play_won_by p all_moves <-> p = player_O.
Proof.
unfold play_won_by, play_won_by_P, play_won_by_O, top.
case: p => //.
Qed.

Lemma bottom_winning_strategy {p} {s : strategy bottom p}
: winning_strategy s <-> p = player_O.
Proof.
unfold winning_strategy.
setoid_rewrite bottom_play_won_by.
firstorder.
eapply H.
apply bottom_player_follows_strategy.
Unshelve.
exact trivial_play.
Qed.

Module Export Notations.
Export game_binding strategy_binding.
Notation "~ g" := (negation g) : game_scope.
Notation "~ s" := (negation_strategy s) : strategy_scope.
End Notations.
End strict.

Module relaxed.
Record game
:= { possible_move : Type
   ; first_player : player
   ; play_won_by_P : Stream possible_move -> Prop
   ; play_won_by_O : Stream possible_move -> Prop
   ; no_duplicate_winner : forall all_moves, play_won_by_P all_moves -> play_won_by_O all_moves -> False
   ; next_player : seq possible_move -> player 
   ; next_move_is_valid : seq possible_move -> possible_move -> bool}.

Definition out_of_turn_move {g} (moves : seq (possible_move g)) (actual_current_player : player) : bool  :=  
actual_current_player != next_player g moves.
(*List.flat_map f s = flatten (List.map f s)*)

Definition strict_moves_to_relaxed_moves_with_player {g : game} (moves : seq (possible_move g * seq (possible_move g))) : seq (possible_move g * player).
refine (flatten _).
refine (map _ (enumerate moves)).
refine (fun '(n, (s0, s)) => _).
refine (let p := if Nat.even n then first_player g else other_player (first_player g) in _).
refine (map _ (s0 :: s)).
refine (fun m => (m, p)). 
Defined.

Fixpoint first_invalid_move_of_relaxed_moves_with_player_helper {g : game} (moves_so_far : seq (possible_move g)) (remaining_moves : seq (possible_move g * player)) : option player := 
match remaining_moves with 
| [::] => None
| (move, p) :: moves => if negb (out_of_turn_move moves_so_far p) && next_move_is_valid g moves_so_far move 
then first_invalid_move_of_relaxed_moves_with_player_helper (rcons moves_so_far move) moves
else Some p
end.
Definition first_invalid_move_of_relaxed_moves_with_player {g : game} (relaxed_moves_with_player : seq (possible_move g * player)) : option player := 
first_invalid_move_of_relaxed_moves_with_player_helper [::] relaxed_moves_with_player.

Definition first_invalid_move {g : game} (moves : seq (possible_move g * seq (possible_move g))) : option player :=
first_invalid_move_of_relaxed_moves_with_player (strict_moves_to_relaxed_moves_with_player moves).
(* for(int i = 0; i <= ; i++)

   {
      for(int j = 0; j <= ; j++)
      {
          if(out_of_turn(moves[0 to i-1] ++ moves[i][0 to j-1], i%2 ) || !next_move_is_valid(moves[0 to i-1] ++ moves[i][0 to j-1], moves[i][j])
              return i%2
      }
   }


[ [(1, 1)] ; [(2, 2)] ; [(0, 2)] ; [(0, 2)] ]


: [ [(1, 1)] ; [(2, 2); (0, 2)] ]
i = 0,j = 0, out of turn ___ (player 0) = false || !next_move_is_valid ___ (1, 1) = false
i = 1,j = 0, outofturn (1, 1) (player 1) = false || !next_move_is_valid (1, 1)(2, 2) = false
i = 1,j = 1, outofturn (1,1)(2, 2) (player 1) = false || !next_move_is_valid (1, 1)(2, 2) = false


 *)
 
Lemma first_invalid_move_of_relaxed_moves_with_player_monotone_app
  {g : game} moves more_moves
: @first_invalid_move_of_relaxed_moves_with_player g moves <> None
 -> first_invalid_move_of_relaxed_moves_with_player (moves ++ more_moves)
  = first_invalid_move_of_relaxed_moves_with_player moves.
Proof.
  unfold first_invalid_move_of_relaxed_moves_with_player.
  set (moves_so_far := [::]); clearbody moves_so_far.
  revert moves_so_far more_moves; induction moves as [|first_move rest_moves]; intros.
  { simpl in *.
    congruence.
  }
  { simpl in *.
    destruct first_move.
    destruct (~~ out_of_turn_move moves_so_far p0 &&
      next_move_is_valid g moves_so_far p).
      { apply IHrest_moves.
       congruence.
      }
      { 
        reflexivity. 
      } 
  }
Qed.
Lemma first_invalid_move_firstn_monotone_succ {g : game} all_moves n
 : @first_invalid_move g (Streams.firstn all_moves n) <> None
    -> first_invalid_move (Streams.firstn all_moves n.+1)
       = first_invalid_move (Streams.firstn all_moves n).
Proof.
  rewrite Streams.firstn_succ.
  generalize (Streams.firstn all_moves n); generalize (Streams.nth all_moves n).
  intros next_move moves_so_far.
  clear all_moves n.
  unfold first_invalid_move.
  unfold strict_moves_to_relaxed_moves_with_player.
  rewrite List.enumerate_rcons map_rcons flatten_rcons.
  apply first_invalid_move_of_relaxed_moves_with_player_monotone_app.
Qed.

Lemma first_invalid_move_firstn_monotone_plus {g : game} all_moves m n
 : @first_invalid_move g (Streams.firstn all_moves n) <> None
    -> first_invalid_move (Streams.firstn all_moves (m + n))
       = first_invalid_move (Streams.firstn all_moves n).
Proof.
  revert all_moves.
  induction m as [|m IHn]; intros all_moves H.
  { reflexivity. }
  { rewrite <- IHn by assumption.
    rewrite (_ : m.+1 + n = (m + n).+1) //.
    rewrite first_invalid_move_firstn_monotone_succ //.
    rewrite IHn //. }
Qed.

Lemma first_invalid_move_firstn_monotone_lt {g : game} all_moves n m
 : (n < m)%coq_nat
    -> @first_invalid_move g (Streams.firstn all_moves n) <> None
    -> first_invalid_move (Streams.firstn all_moves m)
       = first_invalid_move (Streams.firstn all_moves n).
Proof.
  move => Hnm.
  assert (H : m = (m - n) + n) by (rewrite -plusE -minusE; lia).
  rewrite H.
  apply first_invalid_move_firstn_monotone_plus.
Qed.

Definition to_strict (g : game) : strict.game.
refine {| strict.possible_move := possible_move g * seq (possible_move g)
   ; strict.first_player := first_player g
   ; strict.play_won_by_P all_moves := (exists n : nat, first_invalid_move (Streams.firstn all_moves n) == Some player_O) 
   \/ (~(exists n : nat, first_invalid_move (Streams.firstn all_moves n) == Some player_P)
       /\ play_won_by_P g (Streams.flatten all_moves)
    ) 
   ; strict.play_won_by_O all_moves := (exists n : nat, first_invalid_move (Streams.firstn all_moves n) == Some player_P) 
   \/ (~(exists n : nat, first_invalid_move (Streams.firstn all_moves n) == Some player_O)
       /\ play_won_by_O g (Streams.flatten all_moves)
    )
|}.
{ intros all_moves P_winner O_winner.
  destruct P_winner as [P_winner|P_winner], O_winner as [O_winner|O_winner].
  { destruct P_winner as [m P_winner].
    destruct O_winner as [n O_winner].
    (* TODO: check https://stackoverflow.com/q/69350778 to find a more ssreflect-like way to do this *)
    destruct (lt_eq_lt_dec n m) as [[H|H]|H].
    { generalize (first_invalid_move_firstn_monotone_lt all_moves H).
      revert O_winner P_winner.
      move /eqP.
      move ->.
      move /eqP->.
      intuition congruence.
    }
    { subst.
      revert P_winner O_winner.
      move /eqP (* turns first == into = *) -> (* rewrite with first thing *) => // (* finish proof with equality reasoning *) .
    }
    {
      generalize (first_invalid_move_firstn_monotone_lt all_moves H).
      revert O_winner P_winner.
      move /eqP.
      move ->.
      move /eqP->.
      intuition congruence. 
    }
  }
  { destruct O_winner as [a b].
    unfold not in *.
    auto.
  }
  {
    destruct P_winner as [a b].
    unfold not in *.
    auto.
  }
  {
    destruct P_winner as [a b].
    destruct O_winner as [c d].
    eapply (no_duplicate_winner g).
    refine b.
    refine d.
  }
}
   
Defined.

Definition tensor_next_player (p1 : player) (p2 : player) : player := 
match p1, p2 with
| player_P, player_P => player_P
| player_P, player_O => player_P
| player_O, player_P => player_P
| player_O, player_O => player_O
end.

 
Definition left_game_not_abandoned {g1 g2} (all_moves : Stream (strict.possible_move g1 + strict.possible_move g2)) : Prop :=
forall n : nat, exists m : nat, m >= n /\ exists left_move, Streams.nth all_moves m = inl left_move. 

Definition right_game_not_abandoned {g1 g2} (all_moves : Stream (strict.possible_move g1 + strict.possible_move g2)) : Prop :=
forall n : nat, exists m : nat, m >= n /\ exists right_move, Streams.nth all_moves m = inr right_move. 

Lemma left_game_not_abandoned_tl {g1 g2 all_moves}
: @left_game_not_abandoned g1 g2 all_moves -> @left_game_not_abandoned g1 g2 (Streams.tl all_moves).
Proof.
  unfold left_game_not_abandoned.
  intro Hnot_abandoned.
  intro n.
  (* n = m-1 --> n+1 = m *)
  specialize (Hnot_abandoned (n.+1)).
  destruct Hnot_abandoned as [m [Hnm Hnot_abandoned]].
  exists (m.-1).
  revert Hnm Hnot_abandoned.
  case: m => //.
Qed.

Lemma right_game_not_abandoned_tl {g1 g2 all_moves}
: @right_game_not_abandoned g1 g2 all_moves -> @right_game_not_abandoned g1 g2 (Streams.tl all_moves).
Proof.
   unfold right_game_not_abandoned.
  intro Hnot_abandoned.
  intro n.
  (* n = m-1 --> n+1 = m *)
  specialize (Hnot_abandoned (n.+1)).
  destruct Hnot_abandoned as [m [Hnm Hnot_abandoned]].
  exists (m.-1).
  revert Hnm Hnot_abandoned.
  case: m => //.
Qed.

CoInductive moves_compatible_with {g1 g2} (left_moves : strict.play g1) (right_moves : strict.play g2) (all_moves : Stream (strict.possible_move g1 + strict.possible_move g2)) : Prop :=
| moves_compatible_with_left
  : Streams.hd all_moves = inl (Streams.hd left_moves)
    -> moves_compatible_with (Streams.tl left_moves) right_moves (Streams.tl all_moves)
    -> moves_compatible_with left_moves right_moves all_moves
| moves_compatible_with_right
  : Streams.hd all_moves = inr (Streams.hd right_moves)
    -> moves_compatible_with left_moves (Streams.tl right_moves) (Streams.tl all_moves)
    -> moves_compatible_with left_moves right_moves all_moves
.

Lemma left_game_not_abandoned_compatible_with_same_game_ex
  {g1 g2} {left_moves left_moves' : strict.play g1}
: (exists (right_moves right_moves' : strict.play g2) all_moves,
   moves_compatible_with left_moves right_moves all_moves
   /\ moves_compatible_with left_moves' right_moves' all_moves
   /\ left_game_not_abandoned all_moves)
  -> Streams.EqSt left_moves left_moves'.
Proof.
  revert left_moves left_moves'.
  cofix CIH.
  intros left_moves left_moves' Hcompat.
  constructor.
  { 
    destruct Hcompat as [right_moves [right_moves' [all_moves [Hcompat [Hcompat' Hnot_abandoned]]]]].
    specialize (Hnot_abandoned 0).
    destruct Hnot_abandoned as [m Hnot_abandoned].
    destruct Hnot_abandoned as [_ Hnot_abandoned].
    destruct Hnot_abandoned as [left_move Hnot_abandoned].
    clear CIH.
    revert left_moves left_moves' right_moves right_moves' all_moves Hcompat Hcompat' Hnot_abandoned.
    induction m; intros left_moves left_moves' right_moves right_moves' all_moves Hcompat Hcompat' Hnot_abandoned.
    { (* case: proof Hnot_abandoned says that move 0 is in the left game *)
      destruct all_moves, Hcompat, Hcompat'; simpl in *.
      { clear Hcompat Hcompat' Hnot_abandoned. congruence. }
      { congruence. }
      { congruence. }
      { congruence. }
    }
    { (* case: proof Hnot_abandoned says that move m+1 is in the left game *)
      destruct all_moves, Hcompat, Hcompat'; simpl in *.
      { (* case: the first move happened to be in the left game anyway *)
        clear Hcompat Hcompat' Hnot_abandoned. congruence.
      }
      { (* contradiction *) congruence. }
      { (* contradiction *) congruence. }
      { (* case: first move is in the right game *)
        eapply IHm; eassumption.
      }
    }
  }
  {
    (* For arcane Coq reasons, we need to immediately apply CIH.
       Things will be easier if we are left with a single conjunctive goal rather than three separate goals *)
    apply CIH; clear CIH.
    destruct Hcompat as [right_moves [right_moves' [all_moves [Hcompat [Hcompat' Hnot_abandoned]]]]].
    pose proof Hnot_abandoned as Hnot_abandoned'.
    specialize (Hnot_abandoned 0).
    destruct Hnot_abandoned as [m Hnot_abandoned].
    destruct Hnot_abandoned as [_ Hnot_abandoned].
    destruct Hnot_abandoned as [left_move Hnot_abandoned].
    revert left_moves left_moves' right_moves right_moves' all_moves Hcompat Hcompat' Hnot_abandoned Hnot_abandoned'.
    induction m; intros left_moves left_moves' right_moves right_moves' all_moves Hcompat Hcompat' Hnot_abandoned Hnot_abandoned'.
    { (* case: proof Hnot_abandoned says that move 0 is in the left game *)
      destruct all_moves, Hcompat, Hcompat'; simpl in *.
      { apply left_game_not_abandoned_tl in Hnot_abandoned'. 
        simpl in *.
        eauto 10. }
      { congruence. }
      { congruence. }
      { congruence. }
    }
    { (* case: proof Hnot_abandoned says that move m+1 is in the left game *)
      destruct all_moves, Hcompat, Hcompat'; simpl in *.
      { (* case: the first move happened to be in the left game anyway *)
        apply left_game_not_abandoned_tl in Hnot_abandoned'. 
        simpl in *.
        eauto 10.
      }
      { (* contradiction *) congruence. }
      { (* contradiction *) congruence. }
      { (* case: first move is in the right game *)
        apply left_game_not_abandoned_tl in Hnot_abandoned'.
        eapply IHm; eassumption.
      }
    }
  }
Qed. 

Lemma left_game_not_abandoned_compatible_with_same_game
  {g1 g2} {left_moves left_moves' : strict.play g1} {right_moves right_moves' : strict.play g2}
  {all_moves}
: moves_compatible_with left_moves right_moves all_moves
  -> moves_compatible_with left_moves' right_moves' all_moves
  -> left_game_not_abandoned all_moves -> Streams.EqSt left_moves left_moves'.
Proof.
  intros.
  eapply left_game_not_abandoned_compatible_with_same_game_ex.
  eauto 10.
Qed.

Lemma right_game_not_abandoned_compatible_with_same_game_ex
  {g1 g2} {right_moves right_moves' : strict.play g2} 
: (exists (left_moves left_moves' : strict.play g1) all_moves,
   moves_compatible_with left_moves right_moves all_moves
   /\ moves_compatible_with left_moves' right_moves' all_moves
   /\ right_game_not_abandoned all_moves)
  -> Streams.EqSt right_moves right_moves'.
Proof.
  revert right_moves right_moves'.
  cofix CIH.
  intros right_moves right_moves' Hcompat.
  constructor.
  { 
    destruct Hcompat as [left_moves [left_moves' [all_moves [Hcompat [Hcompat' Hnot_abandoned]]]]].
    specialize (Hnot_abandoned 0).
    destruct Hnot_abandoned as [m Hnot_abandoned].
    destruct Hnot_abandoned as [_ Hnot_abandoned].
    destruct Hnot_abandoned as [right_move Hnot_abandoned].
    clear CIH.
    revert right_moves right_moves' left_moves left_moves' all_moves Hcompat Hcompat' Hnot_abandoned.
    induction m; intros right_moves right_moves' left_moves left_moves' all_moves Hcompat Hcompat' Hnot_abandoned.
    { (* case: proof Hnot_abandoned says that move 0 is in the right game *)
      destruct all_moves, Hcompat, Hcompat'; simpl in *.
      { congruence. }
      { congruence. }
      { congruence. }
      { congruence. }
    }
    { (* case: proof Hnot_abandoned says that move m+1 is in the right game *)
      destruct all_moves, Hcompat, Hcompat'; simpl in *.
      { 
        (* case: first move is in the left game *)
        eapply IHm; eassumption.
      }
      { (* contradiction *) congruence. }
      { (* contradiction *) congruence. }
      { (* case: the first move happened to be in the rightgame anyway *)
        clear Hcompat Hcompat' Hnot_abandoned. congruence.
      }
    }
  }
  {
    (* For arcane Coq reasons, we need to immediately apply CIH.
       Things will be easier if we are left with a single conjunctive goal rather than three separate goals *)
    apply CIH; clear CIH.
    destruct Hcompat as [left_moves [left_moves' [all_moves [Hcompat [Hcompat' Hnot_abandoned]]]]].
    pose proof Hnot_abandoned as Hnot_abandoned'.
    specialize (Hnot_abandoned 0).
    destruct Hnot_abandoned as [m Hnot_abandoned].
    destruct Hnot_abandoned as [_ Hnot_abandoned].
    destruct Hnot_abandoned as [right_move Hnot_abandoned].
    revert right_moves right_moves' left_moves left_moves' all_moves Hcompat Hcompat' Hnot_abandoned Hnot_abandoned'.
    induction m; intros right_moves right_moves' left_moves left_moves' all_moves Hcompat Hcompat' Hnot_abandoned Hnot_abandoned'.
    { (* case: proof Hnot_abandoned says that move 0 is in the right game *)
      destruct all_moves, Hcompat, Hcompat'; simpl in *.
      { congruence. }
      { congruence. }
      { congruence. }
      { apply right_game_not_abandoned_tl in Hnot_abandoned'. 
        simpl in *.
        eauto 10. }
    }
    { (* case: proof Hnot_abandoned says that move m+1 is in the left game *)
      destruct all_moves, Hcompat, Hcompat'; simpl in *.
      { (* case: the first move happened to be in the right game anyway *)
        apply right_game_not_abandoned_tl in Hnot_abandoned'. 
        simpl in *.
        eauto 10.
      }
      { (* contradiction *) congruence. }
      { (* contradiction *) congruence. }
      { (* case: first move is in the left game *)
        apply right_game_not_abandoned_tl in Hnot_abandoned'.
        eauto 10.
      }
    }
  }
Qed.

Lemma right_game_not_abandoned_compatible_with_same_game
  {g1 g2} {left_moves left_moves' : strict.play g1} {right_moves right_moves' : strict.play g2}
  {all_moves}
: moves_compatible_with left_moves right_moves all_moves
  -> moves_compatible_with left_moves' right_moves' all_moves
  -> right_game_not_abandoned all_moves -> Streams.EqSt right_moves right_moves'.
Proof.
  intros.
  eapply right_game_not_abandoned_compatible_with_same_game_ex.
  eauto 10.
Qed.

Definition tensor (g1 : strict.game) (g2 : strict.game) : game.
refine {| possible_move := strict.possible_move g1 + strict.possible_move g2 
        ; first_player := tensor_next_player (strict.first_player g1) (strict.first_player g2)
        ; next_player moves_so_far := let (moves_so_far1, moves_so_far2) := partition_map (fun move => move) moves_so_far in
                tensor_next_player (strict.next_player moves_so_far1) (strict.next_player moves_so_far2)
        ; next_move_is_valid moves_so_far next_move := let (moves_so_far1, moves_so_far2) := partition_map (fun move => move) moves_so_far in
               let next_player := tensor_next_player (strict.next_player moves_so_far1) (strict.next_player moves_so_far2) in 
               match next_move with 
               | inl next_move => next_player == strict.next_player moves_so_far1
               | inr next_move => next_player == strict.next_player moves_so_far2
               end
        ; play_won_by_P all_moves := exists right_moves left_moves, moves_compatible_with left_moves right_moves all_moves /\ 
            ((~left_game_not_abandoned all_moves /\ strict.play_won_by_P g2 right_moves)
             \/ (~right_game_not_abandoned all_moves /\ strict.play_won_by_P g1 left_moves)
             \/ (left_game_not_abandoned all_moves /\ right_game_not_abandoned all_moves /\ strict.play_won_by_P g1 left_moves /\ strict.play_won_by_P g2 right_moves))
        ; play_won_by_O all_moves := exists right_moves left_moves, moves_compatible_with left_moves right_moves all_moves /\ 
            ((right_game_not_abandoned all_moves /\ strict.play_won_by_O g2 right_moves)
             \/ (left_game_not_abandoned all_moves /\ strict.play_won_by_O g1 left_moves))
        |}.
  { intros all_moves P_winner O_winner.
    destruct P_winner as [right_moves P_winner].
    destruct P_winner as [left_moves P_winner].
    destruct O_winner as [right_moves' O_winner].
    destruct O_winner as [left_moves' O_winner].
    destruct P_winner as [hp_compatible P_winner].
    destruct O_winner as [ho_compatible O_winner].
    destruct P_winner as [P_winner | P_winner].
    {
      destruct O_winner as [O_winner | O_winner].
      {
        destruct P_winner as [left_abandoned right_P_winner].
        destruct O_winner as [right_not_abandoned right_O_winner].
        assert (right_moves = right_moves').
        {
          apply Streams.extensionality.
          eapply right_game_not_abandoned_compatible_with_same_game.
          {
            exact hp_compatible.
          }
          {
            exact ho_compatible.
          }
          {
            exact right_not_abandoned.
          }
        }
        subst right_moves'.
        eapply (strict.no_duplicate_winner g2).
        {
          exact right_P_winner.
        }
        {
          exact right_O_winner.
        }
      }
      {
        tauto.
      }
     }
     {
       destruct P_winner as [P_winner | P_winner].
       {
         destruct O_winner as [O_winner | O_winner].
         {
           tauto.
         }
         {
           destruct P_winner as [right_abandoned left_P_winner].
           destruct O_winner as [left_not_abandoned left_O_winner].
           assert (left_moves = left_moves').
         {
           apply Streams.extensionality.
          eapply left_game_not_abandoned_compatible_with_same_game.
          {
            exact hp_compatible.
          }
          {
            exact ho_compatible.
          }
          {
            exact left_not_abandoned.
          }
        }
        subst left_moves'.
        eapply (strict.no_duplicate_winner g1).
        {
          exact left_P_winner.
        }
        {
          exact left_O_winner.
        }
      }
    }
    {
      destruct P_winner as [left_not_abandoned P_winner]. 
      destruct P_winner as [right_not_abandoned P_winner].
      destruct P_winner as [left_P_winner right_P_winner].
      destruct O_winner as [O_winner | O_winner].
      {
        destruct O_winner as [right_not_abandoned' right_O_winner].
        assert (right_moves = right_moves').
        { eapply Streams.extensionality, right_game_not_abandoned_compatible_with_same_game; eassumption. }
        subst right_moves'.
        eapply strict.no_duplicate_winner; eassumption.
      }
      {
        destruct O_winner as [left_not_abandoned' left_O_winner].
        assert (left_moves = left_moves').
        { eapply Streams.extensionality, left_game_not_abandoned_compatible_with_same_game; eassumption. }
        subst left_moves'.
        eapply (strict.no_duplicate_winner g1); eassumption.      
       }
     } 
   }
 }
Defined.

Definition strict_tensor (g1 : strict.game) (g2 : strict.game) : strict.game :=
 to_strict (tensor g1 g2).
Import strict.Notations.
Print Grammar constr.
Infix "*" := strict_tensor : game_scope.
Infix "⊗" := strict_tensor (at level 40, left associativity) : game_scope.
Check (_ * _)%game.

Definition strict_par (g1 : strict.game) (g2 : strict.game) : strict.game := 
~((~g1) ⊗ (~g2)).

Infix "~*" := strict_par (at level 40, left associativity) : game_scope.

Module Export Notations.
Export strict.Notations.
Infix "*" := strict_tensor : game_scope.
Infix "⊗" := strict_tensor (at level 40, left associativity) : game_scope.
Infix "~*" := strict_par (at level 40, left associativity) : game_scope.
End Notations. 
End relaxed.

Module tic_tac_toe_relaxed.
Definition tic_tac_toe_game : relaxed.game.
refine {| relaxed.possible_move := nat * nat
        ; relaxed.first_player := player_P
        ; relaxed.next_player moves_so_far := if Nat.even (List.length moves_so_far) then player_P else player_O
        ; relaxed.play_won_by_P all_moves := exists n : nat, tic_tac_toe.game_outcome (Streams.firstn all_moves n) tic_tac_toe.initial_state == Some tic_tac_toe.player_1
        ; relaxed.play_won_by_O all_moves := exists n : nat, tic_tac_toe.game_outcome (Streams.firstn all_moves n) tic_tac_toe.initial_state == Some tic_tac_toe.player_2
        ; relaxed.no_duplicate_winner all_moves P_winner O_winner := _
        ; relaxed.next_move_is_valid := tic_tac_toe.next_move_is_valid_or_game_finished
        |}.
{ simpl in *.
  (* TODO: Homework *) 

Admitted.
End tic_tac_toe_relaxed.

Module affine.
Section with_variables.
Context {var : Type}.
Inductive syntax := Var (v : var)
 | Zero | One 
 | Tensor (Left : syntax) (Right : syntax)
 (*| With (Left : syntax) (Right : syntax)
 | Implication (Left : syntax) (Right : syntax)
 | Bang (Right : syntax)*).
End with_variables.
Global Arguments syntax : clear implicits.
Module Export SyntaxNotations.
Declare Scope syntax_scope.
Delimit Scope syntax_scope with syntax. (* allows writing foo%syntax to mean that foo is in syntax_scope *)
Bind Scope syntax_scope with syntax. (* means that functions taking variables of type syntax will
automatically parse those variables in syntax_scope *)
Print Grammar constr.
Notation "A * B" := (Tensor A B) : syntax_scope.
(*Notation "A && B" := (With A B) : syntax_scope.
Notation "A '-o' B" := (Implication A B) (at level 99) : syntax_scope.
Notation "! A" := (Bang A) (at level 9, format "! A") : syntax_scope.*)
Notation "0" := Zero : syntax_scope.
Notation "1" := One : syntax_scope.
Reserved Notation "Ctx ||- A" (at level 100, no associativity).
End SyntaxNotations.
Scheme Equality for syntax.

(* ssreflect magic to use decidable membership *)
Lemma syntax_eqbP
  {var} {var_beq : var -> var -> bool}
  (H : Equality.axiom var_beq)
 : Equality.axiom (syntax_beq var_beq).
Proof.
  intros A B;
  unshelve (
  epose proof (@internal_syntax_dec_bl var var_beq _ A B);
  epose proof (@internal_syntax_dec_lb var var_beq _ A B)
  ).
  { move => x y p; specialize (H x y); revert p H.
    move => -> H; inversion H; assumption. }
  { move => x y <-; specialize (H x x).
    inversion H; congruence. }
  destruct (@syntax_beq var var_beq A B); constructor.
  all: intuition congruence.
Qed.
Module Export Canonical.
Canonical syntax_eqMixin {var var_beq var_eqP} := EqMixin (@syntax_eqbP var var_beq var_eqP).
Canonical syntax_eqType {var var_beq var_eqP} := Eval hnf in EqType (syntax var) (@syntax_eqMixin var var_beq var_eqP).
End Canonical.
Module Export Exports.
Export SyntaxNotations.
Export Canonical.
End Exports.
End affine.
(*
Inductive var := tic_tac_toe | nim | chess.
Definition var_to_game (v : var) : strict.game :=
match v with
| tic_tac_toe => tic_tac_toe.tic_tac_toe_strict_game
| nim => nim.nim_strict_game
| chess => chess.chess_strict_game
end.
*)
Module affine_to_game.
Import strict.Notations relaxed.Notations affine.Exports.
Section with_var.
Context {var : Type} (var_to_game : var -> strict.game).
Fixpoint syntax_to_game (s : affine.syntax var) : strict.game :=
match s with
 | affine.Var v => var_to_game v
 | affine.Zero => strict.bottom
 | affine.One => strict.top
 | affine.Tensor Left Right => syntax_to_game Left ⊗ syntax_to_game Right
end.

(* Given A, B, C, ..., D ||- G, we want to translate this into
    G ~* (~A) ~* (~B) ~* (~C) ~* ...~* (~D) 
    assumptions = A, B, C, ..., D
    conclusion  = G
    *)
Local Open Scope game_scope.
Definition sequent_to_game (assumptions : seq (affine.syntax var)) (conclusion : affine.syntax var) : strict.game :=
  foldl (fun g1 g2 => (g1) ~* (g2))
        (syntax_to_game conclusion)
        (map (fun g => ~syntax_to_game g) assumptions). (*to negate the elements in the sequence*)
Eval cbv [foldr foldl sequent_to_game map] in sequent_to_game [:: ?[A] ; ?[B] ; ?[C] ; ?[D] ] ?[G].
Print Assumptions sequent_to_game.
(*
Lemma provable_to_winning_strategy {assumptions conclusion}
: (assumptions ||- conclusion) -> exists s : strategy (sequent_to_game assumptions conclusion), winning_strategy s.
*)
(*
Lemma winning_strategy_to_provable {assumptions conclusion}
  (H : assumptions and conclusion are in the appropriately restricted fragment)
: (exists s : strategy (sequent_to_game assumptions conclusion), winning_strategy s) -> (assumptions ||- conclusion).
*)
End with_var.
End affine_to_game.



