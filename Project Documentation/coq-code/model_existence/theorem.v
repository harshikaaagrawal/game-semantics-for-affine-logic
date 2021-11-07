
Fixpoint truth_value (x : syntax) : bool
  := match x with
     | One  => true
     | Zero => false
     | Tensor l r => truth_value l && truth_value r
     | With l r   => truth_value l && truth_value r
     | Implication l r => if truth_value l then truth_value r else true
     | Bang r => truth_value r
     end.

Definition truth_value_of_context (ctx : seq syntax) : bool
  := foldr andb true (map truth_value ctx).
  
Theorem model : forall {Ctx P},
  (Ctx ||- P) -> truth_value_of_context Ctx = true -> truth_value P = true.