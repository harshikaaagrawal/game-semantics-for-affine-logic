Proof.
  intros Ctx P H T.
  induction H;
  rewrite -> ?truth_value_of_context_cat,
    -> ?truth_value_of_context_cons,
    -> ?truth_value_of_context_nil,
    -> ?Bool.andb_true_r in *.
  all: simpl in *; auto.  
  all: rewrite -> ?truth_value_of_context_cat,
         -> ?truth_value_of_context_cons,
         -> ?truth_value_of_context_nil,
         -> ?Bool.andb_true_r in *.
  all: simpl in *; auto.  
  {
    apply truth_value_of_context_perm in a.
    rewrite -a // in T.
  }
  {
    rewrite -> ?Bool.andb_assoc in *.    
    assert (X : truth_value A = true) by auto.
    rewrite -> X in *.
    auto.
  }
  {
    rewrite T in IHprovable.
    Search (_ && true).
    rewrite -> Bool.andb_true_r in *.
    destruct (truth_value A); auto.
  }
Qed.