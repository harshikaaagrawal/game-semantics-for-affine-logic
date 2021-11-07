Lemma top_play_won_by {p} {all_moves : play top}
 : play_won_by p all_moves <-> p = player_P.
Proof.
  unfold play_won_by, play_won_by_P, play_won_by_O, top.
  case: p => //.
Qed.