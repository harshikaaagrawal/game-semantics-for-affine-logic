Notation "A * B" := (Tensor A B) : syntax_scope.
Notation "A && B" := (With A B) : syntax_scope.
Notation "A '-o' B" := (Implication A B) (at level 99) : syntax_scope.
Notation "! A" := (Bang A) (at level 9, format "! A") : syntax_scope.
Notation "0" := Zero : syntax_scope.
Notation "1" := One : syntax_scope.