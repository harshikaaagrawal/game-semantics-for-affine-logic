Lemma bottom_play_won_by {p} {all_moves : play bottom}
 : play_won_by p all_moves <-> p = player_O.
Proof.
  unfold play_won_by, play_won_by_P, play_won_by_O, top.
  case: p => //.
Qed.