Lemma bottom_winning_strategy {p} {s : strategy bottom p}
 : winning_strategy s <-> p = player_O.
Proof.
  unfold winning_strategy.
  setoid_rewrite bottom_play_won_by.
  firstorder.
  eapply H.
  apply bottom_player_follows_strategy.
  Unshelve.
  exact trivial_play.
Qed. 