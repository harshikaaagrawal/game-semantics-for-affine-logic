Lemma top_player_follows_strategy {p} {s : strategy top p} {all_moves : play top} 
: player_follows_strategy p s all_moves.
Proof.
  unfold player_follows_strategy.
  intros n Hp.
  destruct (Streams.nth all_moves n.+1).
  destruct (s (Streams.firstn all_moves n)).
  reflexivity.
Qed.