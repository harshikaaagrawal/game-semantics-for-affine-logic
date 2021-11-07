Inductive syntax {var : Type} :=
| Var (v : var)
| Zero (* 0 *)
| One  (* 1 *)
| Tensor (Left : syntax) (Right : syntax) (* ⊗ *)
| With   (Left : syntax) (Right : syntax) (* & *)
| Implication (Left : syntax) (Right : syntax) (* ⊸ *)
| Bang (Right : syntax) (* ! *)
.