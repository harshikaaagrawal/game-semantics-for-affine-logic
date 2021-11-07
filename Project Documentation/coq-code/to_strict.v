Definition out_of_turn_move {g}
  (moves : seq (possible_move g)) (actual_current_player : player) : bool
   := actual_current_player != next_player g moves.

Definition strict_moves_to_relaxed_moves_with_player {g : game}
  (moves : seq (possible_move g * seq (possible_move g)))
    : seq (possible_move g * player)
  := flatten (map (fun '(n, (s0, s)) =>
       let p := if Nat.even n
                then first_player g
                else other_player (first_player g) in
       map (fun m => (m, p)) (s0 :: s))
      (enumerate moves)).

Fixpoint first_invalid_move_of_relaxed_moves_with_player_helper {g : game}
  (moves_so_far : seq (possible_move g))
  (remaining_moves : seq (possible_move g * player))
   : option player := 
  match remaining_moves with 
  | [::] => None
  | (move, p) :: moves => 
     if negb (out_of_turn_move moves_so_far p)
         && next_move_is_valid g moves_so_far move 
     then first_invalid_move_of_relaxed_moves_with_player_helper 
       (rcons moves_so_far move) moves
     else Some p
  end.
Definition first_invalid_move_of_relaxed_moves_with_player {g : game}
  (relaxed_moves_with_player : seq (possible_move g * player)) : option player
  := first_invalid_move_of_relaxed_moves_with_player_helper
       [::] relaxed_moves_with_player.

Definition first_invalid_move {g : game}
  (moves : seq (possible_move g * seq (possible_move g))) : option player
 := first_invalid_move_of_relaxed_moves_with_player
      (strict_moves_to_relaxed_moves_with_player moves).  

Lemma first_invalid_move_firstn_monotone_lt {g : game} all_moves n m
 : (n < m)%coq_nat
    -> @first_invalid_move g (Streams.firstn all_moves n) <> None
    -> first_invalid_move (Streams.firstn all_moves m)
       = first_invalid_move (Streams.firstn all_moves n).
       
Definition to_strict (g : game) : strict.game.
refine {| strict.possible_move := possible_move g * 
  seq (possible_move g);
    strict.first_player := first_player g
   ; strict.play_won_by_P all_moves
      := (exists n : nat,
            first_invalid_move (Streams.firstn all_moves n) 
              == Some player_O) 
   \/ (~(exists n : nat,
          first_invalid_move (Streams.firstn all_moves n) 
            == Some player_P)
       /\ play_won_by_P g (Streams.flatten all_moves)
    ) 
   ; strict.play_won_by_O all_moves
      := (exists n : nat,
           first_invalid_move (Streams.firstn all_moves n) 
             == Some player_P) 
   \/ (~(exists n : nat,
           first_invalid_move (Streams.firstn all_moves n) 
             == Some player_O)
       /\ play_won_by_O g (Streams.flatten all_moves)
    )
|}.