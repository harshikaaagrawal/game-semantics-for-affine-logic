Lemma negation_player_follows_strategy {g} {p} {s : strategy g p} {all_moves : play g} 
: player_follows_strategy p s all_moves
   <-> player_follows_strategy (~p) (~s) all_moves.
Proof.
  unfold player_follows_strategy.
  apply forall_iff_compat.
  intro n.
  apply imp_iff_compat_r.
  unfold next_player.
  simpl.
  generalize (Nat.even (Datatypes.length (Streams.firstn all_moves n)));
    intro fp_move.
  generalize (first_player g); intro fp.
  Local Open Scope player_scope.
  destruct fp_move, fp, p.
  all: simpl.
  all: done.
Qed.