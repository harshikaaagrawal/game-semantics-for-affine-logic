Definition tic_tac_toe_game : relaxed.game.
refine {|
   relaxed.possible_move := nat * nat
 ; relaxed.first_player := player_P
 ; relaxed.next_player moves_so_far := if Nat.even (List.length moves_so_far) 
                                       then player_P else player_O
 ; relaxed.play_won_by_P all_moves 
   := exists n : nat,
     tic_tac_toe.game_outcome
       (Streams.firstn all_moves n) tic_tac_toe.initial_state
     == Some tic_tac_toe.player_1
 ; relaxed.play_won_by_O all_moves 
   := exists n : nat,
     tic_tac_toe.game_outcome
       (Streams.firstn all_moves n) tic_tac_toe.initial_state
     == Some tic_tac_toe.player_2
 ; relaxed.next_move_is_valid := tic_tac_toe.next_move_is_valid_or_game_finished
  |}.