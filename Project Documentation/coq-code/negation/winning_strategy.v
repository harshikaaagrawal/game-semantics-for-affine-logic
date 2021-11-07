Lemma negation_winning_strategy {g} {p} {s : strategy g p}
  : winning_strategy s <-> winning_strategy (~s).
Proof.
  unfold winning_strategy.
  unfold winning_strategy.
  apply forall_iff_compat; intro w.
  rewrite <- negation_player_follows_strategy.
  apply imp_iff_compat_l.
  apply negation_play_won_by.
Qed.