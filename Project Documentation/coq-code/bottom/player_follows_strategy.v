Lemma bottom_player_follows_strategy {p} {s : strategy bottom p} {all_moves : play bottom} 
: player_follows_strategy p s all_moves.
Proof.
  unfold player_follows_strategy.
  intros n Hp.
  destruct (Streams.nth all_moves n.+1).
  destruct (s (Streams.firstn all_moves n)).
  reflexivity.
Qed.