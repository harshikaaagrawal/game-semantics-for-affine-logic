Definition top : game.
refine {| possible_move := unit 
        ; first_player := player_P
        ; play_won_by_P all_moves := True
        ; play_won_by_O all_moves := False 
        ; no_duplicate_winner all_moves P_wins O_wins := O_wins    
|}.
Defined.    

Definition bottom : game.
refine {| possible_move := unit
        ; first_player := player_O
        ; play_won_by_P all_moves := False
        ; play_won_by_O all_moves := True
        ; no_duplicate_winner all_moves P_wins O_wins := P_wins
|}.
Defined.    
    
Definition negation (g : game) : game.
refine {| possible_move := possible_move g
        ; first_player := other_player (first_player g)
        ; play_won_by_P all_moves := play_won_by_O g all_moves 
        ; play_won_by_O all_moves := play_won_by_P g all_moves
        ; no_duplicate_winner all_moves P_winner O_winner 
          := no_duplicate_winner g all_moves O_winner P_winner |}.
Defined.
Notation "~ g" := (negation g) : game_scope.

Definition strict_par (g1 : strict.game) (g2 : strict.game) : strict.game 
  := ~((~g1) ⊗ (~g2)).
Infix "~*" := strict_par (at level 40, left associativity) : game_scope.


Definition strict_tensor (g1 : strict.game) (g2 : strict.game) : strict.game 
  := to_strict (tensor g1 g2).
Infix "⊗" := strict_tensor (at level 40, left associativity) : game_scope.