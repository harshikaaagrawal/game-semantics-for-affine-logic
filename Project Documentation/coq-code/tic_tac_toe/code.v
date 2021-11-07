Module tic_tac_toe.
Notation new_line := (String "010" EmptyString) (only parsing).

Inductive player := player_1 | player_2.
Definition cell := option player.
Definition cell_to_string (c : cell) : string := 
  match c with
  |None => " "
  |Some player_1 => "X"
  |Some player_2 => "O"
  end.
Definition board := seq (seq cell).
Definition empty : cell := None.
Coercion some_player (p : player) : cell := Some p.
Definition set_cell (b : board) (r : nat) (c : nat) (p : player) : board 
  := set_nth [::] b r (set_nth empty (nth [::] b r) c p).
Definition get_cell (b : board) (r : nat) (c : nat) : cell 
  := nth empty (nth [::] b r ) c.
Definition get_column (b : board) (c : nat) : seq cell 
  := map (fun r => get_cell b r c) [:: 0 ; 1 ; 2 ].
Definition rows (b: board) : seq (seq cell) := b.
Definition columns (b : board) : seq (seq cell) := 
  map (fun c => get_column b c) [:: 0 ; 1 ; 2 ].
Definition diagonals (b : board) : seq (seq cell) 
  := [:: [:: get_cell b 0 0 ; get_cell b 1 1 ; get_cell b 2 2] 
      ; [:: get_cell b 0 2 ; get_cell b 1 1 ; get_cell b 2 0] ].
Definition cells_same_non_empty (s : seq cell) : bool 
  := foldr andb true (map (fun c => c == nth empty s 0) s)
     && (nth empty s 0 != empty).
Definition any_cells_same_non_empty (s : seq (seq cell)) : bool := 
  foldr orb false (map cells_same_non_empty s).
Definition any_row (b: board) : bool := 
  any_cells_same_non_empty (rows b).
Definition any_column (b : board) : bool := 
  any_cells_same_non_empty (columns b).
Definition any_diagonal (b : board) : bool 
  := any_cells_same_non_empty (diagonals b).
Definition other_player (current_player : player) : player 
  := match current_player with
     |player_1 => player_2
     |player_2 => player_1
     end.
Definition initial_board : board 
  := nseq 3 (nseq 3 empty).
Definition output_row (s: seq cell) : string 
  := foldr String.append ""%string (map cell_to_string s) ++ new_line.
Definition output_board (b : board) : string := 
  foldr String.append ""%string (map output_row b).
Definition game_result (state : board * player) : option player
  := let (b, current_player) := state in
     if any_row b || any_column b 
        || any_diagonal b
     then Some (other_player current_player)
     else None.
Definition initial_state : board * player 
  := (initial_board, player_1).
Definition game_result_string (p : option player) : string := later.
Definition game_intro : string := later.
Definition main_game (b : board) : unit := later.
Definition input_and_make_move (current_player : player) (b : board)
  : player * board := later.
Definition move_is_valid (b : board) (r : nat) (c : nat) : bool 
  := (r <= 3) && (c <= 3) && (get_cell b r c == empty).
Definition make_move (b: board) (current_player : player) 
           (r : nat) (c : nat) : board * bool 
  := if move_is_valid b r c
     then (set_cell b r c current_player, true)
     else (b, false).
Definition make_single_move (state : board*player) (next_move : nat*nat)
  : (board*player)*bool 
  := let (r, c) := next_move in
     let (b, p) := state in 
     let (new_board, is_valid) 
         := make_move b p r c in 
     ((new_board, other_player p), is_valid).
Fixpoint make_moves (moves : seq (nat*nat)) (state : board*player) : board*player 
  := match moves with
     |[::] => state
     |move :: moves =>
      let new_state := fst (make_single_move state move) in
      make_moves moves new_state
     end.

Definition next_move_is_valid
  (moves_so_far : seq (nat * nat)) (next_move : nat * nat) : bool 
  := let (r, c) := next_move in 
     let (b, _) := make_moves moves_so_far initial_state in 
     move_is_valid b r c.

Fixpoint game_outcome (moves : seq (nat * nat)) (state : board*player) : option player 
  := (*None means game is still in progress,
       some player means game is over and that player won*)
    match moves with 
    | [::] => None 
    | move :: moves =>
      let (new_state, is_valid) := make_single_move state move in 
      if is_valid 
      then match game_result new_state with 
           | None => game_outcome moves new_state
           | Some winner => Some winner
           end
      else
        Some (other_player (snd state)) 
    end.

Compute output_board 
  (fst (make_move initial_board player_1 1 2) ).
Compute output_board
  (fst (make_move (fst (make_move initial_board player_1 1 2)) player_2 1 1) ).
Compute output_board
  (fst (make_moves [:: (1, 1) ; (2, 2) ; (1, 0) ; (0,0) ; (1, 2)] initial_state)).
Compute game_result
  (make_moves [:: (1, 1) ; (2, 2) ; (1, 0) ; (0,0) ; (1, 2)] initial_state).

Definition next_move_is_valid_or_game_finished (moves_so_far : seq (nat * nat))
  (next_move : nat * nat) : bool 
  := next_move_is_valid moves_so_far next_move
     || (game_outcome moves_so_far initial_state != None).

End tic_tac_toe.