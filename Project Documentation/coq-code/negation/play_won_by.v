Lemma negation_play_won_by {g} {p} {all_moves : play g}
 : play_won_by p all_moves <-> play_won_by (g:=~g) (~ p) all_moves.
Proof.
  unfold play_won_by in *.
  simpl.
  destruct p.
  { simpl.
    reflexivity.
  }
  { simpl.
    reflexivity.
  }
Qed.