Inductive player := player_O | player_P.

Record game
:= { possible_move : Type
   ; first_player : player
   ; play_won_by_P : Stream possible_move -> Prop
   ; play_won_by_O : Stream possible_move -> Prop
   ; no_duplicate_winner : forall all_moves,
      play_won_by_P all_moves -> play_won_by_O all_moves -> False
   }.