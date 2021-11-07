Definition position (g : game) : Type
  := seq (possible_move g).

Definition play (g : game) : Type
  := Stream (possible_move g).

Definition next_player {g} (p : position g) : player
  := if Nat.even (List.length p)
     then first_player g
     else other_player (first_player g).

Definition strategy g (p : player) : Type
  := forall (pos : position g), possible_move g.

Definition player_follows_strategy
 {g} (p : player) (s : strategy g p) (all_moves : play g) : Prop
  := forall n : nat, let initial_segment := Streams.firstn all_moves n in 
     forall h : next_player initial_segment == p, 
     Streams.nth all_moves (n.+1) = s initial_segment.

Definition play_won_by {g} (p : player) (all_moves : play g) : Prop
  := match p with
     | player_P => play_won_by_P g all_moves
     | player_O => play_won_by_O g all_moves
     end.

Definition winning_strategy {g} {p : player} (s : strategy g p) : Prop
  := forall all_moves : play g,
     player_follows_strategy p s all_moves -> play_won_by p all_moves. 