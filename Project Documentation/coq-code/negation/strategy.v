Definition negation_strategy {g} {p} (s : strategy g p) : strategy (~g) (~p) := s.
Notation "~ s" := (negation_strategy s) : strategy_scope.