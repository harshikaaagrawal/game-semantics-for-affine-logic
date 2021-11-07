
Context {var : Type} (var_to_game : var -> strict.game).
Fixpoint syntax_to_game (s : @affine.syntax var) : strict.game :=
match s with
 | affine.Var v => var_to_game v
 | affine.Zero => strict.bottom
 | affine.One => strict.top
 | affine.Tensor Left Right => syntax_to_game Left ⊗ syntax_to_game Right
end.

Definition sequent_to_game (context : seq (@affine.syntax var)) 
  (result : @affine.syntax var) : strict.game :=
  foldl (fun g1 g2 => (g1) ~* (g2))
        (syntax_to_game result)
        (map (fun g => ~syntax_to_game g) context).