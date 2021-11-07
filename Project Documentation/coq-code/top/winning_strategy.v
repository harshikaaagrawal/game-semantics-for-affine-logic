Lemma top_winning_strategy {p} {s : strategy top p}
 : winning_strategy s <-> p = player_P.
Proof.
  unfold winning_strategy.
  setoid_rewrite top_play_won_by.
  firstorder.
  eapply H.
  apply top_player_follows_strategy.
  Unshelve.
  exact trivial_play.
Qed. 