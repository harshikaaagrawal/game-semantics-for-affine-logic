Module relaxed.
Record game
:= { possible_move : Type
   ; first_player : player
   ; play_won_by_P : Stream possible_move -> Prop
   ; play_won_by_O : Stream possible_move -> Prop
   ; no_duplicate_winner : forall all_moves, 
       play_won_by_P all_moves -> play_won_by_O all_moves -> False
   ; next_player : seq possible_move -> player 
   ; next_move_is_valid : seq possible_move -> possible_move -> bool}.