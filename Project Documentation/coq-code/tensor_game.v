Definition tensor_next_player (p1 : player) (p2 : player) : player 
  := match p1, p2 with
| player_P, player_P => player_P
| player_P, player_O => player_P
| player_O, player_P => player_P
| player_O, player_O => player_O
end.

 
Definition left_game_not_abandoned {g1 g2}
  (all_moves : Stream (strict.possible_move g1 + strict.possible_move g2)) 
    : Prop := forall n : nat, exists m : nat, m >= n 
  /\ exists left_move, Streams.nth all_moves m = inl left_move. 

Definition right_game_not_abandoned {g1 g2} 
  (all_moves : Stream (strict.possible_move g1 + strict.possible_move g2)) 
    : Prop := forall n : nat, exists m : nat, m >= n 
  /\ exists right_move, Streams.nth all_moves m = inr right_move. 

Lemma left_game_not_abandoned_tl {g1 g2 all_moves}
: @left_game_not_abandoned g1 g2 all_moves
  -> @left_game_not_abandoned g1 g2 (Streams.tl all_moves).
  
Lemma right_game_not_abandoned_tl {g1 g2 all_moves}
: @right_game_not_abandoned g1 g2 all_moves 
  -> @right_game_not_abandoned g1 g2 (Streams.tl all_moves).

CoInductive moves_compatible_with {g1 g2}
  (left_moves : strict.play g1) (right_moves : strict.play g2) 
  (all_moves : Stream (strict.possible_move g1 + strict.possible_move g2))
    : Prop :=
| moves_compatible_with_left
 : Streams.hd all_moves = inl (Streams.hd left_moves)
   -> moves_compatible_with 
       (Streams.tl left_moves) right_moves (Streams.tl all_moves)
   -> moves_compatible_with left_moves right_moves all_moves
| moves_compatible_with_right
 : Streams.hd all_moves = inr (Streams.hd right_moves)
   -> moves_compatible_with left_moves
       (Streams.tl right_moves) (Streams.tl all_moves)
   -> moves_compatible_with left_moves right_moves all_moves.

Lemma left_game_not_abandoned_compatible_with_same_game_ex
  {g1 g2} {left_moves left_moves' : strict.play g1}
: (exists (right_moves right_moves' : strict.play g2) all_moves,
   moves_compatible_with left_moves right_moves all_moves
   /\ moves_compatible_with left_moves' right_moves' all_moves
   /\ left_game_not_abandoned all_moves)
  -> Streams.EqSt left_moves left_moves'.
  
Lemma left_game_not_abandoned_compatible_with_same_game
  {g1 g2} {left_moves left_moves' : strict.play g1} 
    {right_moves right_moves' : strict.play g2} {all_moves}
: moves_compatible_with left_moves right_moves all_moves
  -> moves_compatible_with left_moves' right_moves' all_moves
  -> left_game_not_abandoned all_moves
  -> Streams.EqSt left_moves left_moves'.
  
Lemma right_game_not_abandoned_compatible_with_same_game_ex
  {g1 g2} {right_moves right_moves' : strict.play g2}
: (exists (left_moves left_moves' : strict.play g1) all_moves,
   moves_compatible_with left_moves right_moves all_moves
   /\ moves_compatible_with left_moves' right_moves' all_moves
   /\ right_game_not_abandoned all_moves)
  -> Streams.EqSt right_moves right_moves'.
  
Lemma right_game_not_abandoned_compatible_with_same_game
  {g1 g2} {left_moves left_moves' : strict.play g1} 
    {right_moves right_moves' : strict.play g2}
  {all_moves}
: moves_compatible_with left_moves right_moves all_moves
  -> moves_compatible_with left_moves' right_moves' all_moves
  -> right_game_not_abandoned all_moves
  -> Streams.EqSt right_moves right_moves'.
  
Definition tensor (g1 : strict.game) (g2 : strict.game) : game.
refine {|
   possible_move := strict.possible_move g1 + strict.possible_move g2
 ; first_player
   := tensor_next_player (strict.first_player g1) (strict.first_player g2)
 ; next_player moves_so_far
   := let (moves_so_far1, moves_so_far2)
          := partition_map (fun move => move) moves_so_far in
      tensor_next_player (strict.next_player moves_so_far1)
                         (strict.next_player moves_so_far2)
 ; next_move_is_valid moves_so_far next_move
   := let (moves_so_far1, moves_so_far2)
          := partition_map (fun move => move) moves_so_far in
      let next_player
          := tensor_next_player
               (strict.next_player moves_so_far1) (strict.next_player moves_so_far2)
      in
      match next_move with
      | inl next_move => next_player == strict.next_player moves_so_far1
      | inr next_move => next_player == strict.next_player moves_so_far2
      end
 ; play_won_by_P all_moves
   := exists right_moves left_moves,
     moves_compatible_with left_moves right_moves all_moves
     /\ ((~left_game_not_abandoned all_moves
          /\ strict.play_won_by_P g2 right_moves)
         \/ (~right_game_not_abandoned all_moves
             /\ strict.play_won_by_P g1 left_moves)
         \/ (left_game_not_abandoned all_moves
             /\ right_game_not_abandoned all_moves
             /\ strict.play_won_by_P g1 left_moves
             /\ strict.play_won_by_P g2 right_moves))
 ; play_won_by_O all_moves
   := exists right_moves left_moves,
     moves_compatible_with left_moves right_moves all_moves
     /\ ((right_game_not_abandoned all_moves
          /\ strict.play_won_by_O g2 right_moves)
         \/ (left_game_not_abandoned all_moves
             /\ strict.play_won_by_O g1 left_moves))
  |}.