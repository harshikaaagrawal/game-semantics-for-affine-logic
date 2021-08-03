Print bool.
Inductive mybool := mytrue | myfalse.
Print mybool.

Inductive datatype := value1 | value2 | value3.
Print datatype.

Record three_bools := { bool1 : bool ; bool2 : bool ; bool3 : bool }.
Print three_bools.
Inductive three_bools' :=
| Build_three_bools' (bool1 : bool) (bool2 : bool) (boo3 : bool).
Print three_bools'.

Definition datatype_to_nat (v : datatype) : nat :=
  match v with
  | value1 => 1 
  | value2 => 2
  | value3 => 3
  end.

Compute datatype_to_nat value1.
Compute datatype_to_nat ?[v].

Print option.
Print list.

Require Coq.Vectors.Vector.
Print Vector.t.
Locate "*".
Print "*"%type.
Print prod.
Check prod nat (Vector.t bool ?[n]).
Print sigT.
Check @sigT nat (fun n => Vector.t bool n).
Check exists n : nat, n * n = 4.
Locate "exists".
Print ex.

Require Import Coq.Program.Equality.

Module Syntax1.
(* int x = 5 + 6 * 7 *)
(*       =
       /         \
    int x      5 + 6 * 7
     /  \           /   \
   int   x          5   6*7
                        /   \
                        6   7
*)
(* True /\ (True \/ False) -> True
     /                          \
True /\ (True \/ False)         True
   /                \           
   True          True \/ False
                    /    \
                   True    False
*)
(*            "->"
       /            \
    "/\"           "True"
/        \
"True"   "\/"
         /  \
    "True" "False"
*)
Inductive syntax := True | False 
 | And (Left : syntax) (Right : syntax)
 | Or (Left : syntax) (Right : syntax)
 | Implication (Left : syntax) (Right : syntax)
 | Negation (Right : syntax) 
 | Biconditional (Left : syntax) (Right : syntax).

Inductive provable : syntax -> Type :=
| Trivial : provable True
| And_intro Left Right (a : provable Left) (b : provable Right): provable (And Left Right)
| And_use_left Left Right (a : provable (And Left Right)) : provable Left
| And_use_right Left Right (a: provable (And Left Right)) : provable Right
| Or_intro Left Right (a : provable Left) (b : provable Right): provable (Or Left Right)
| Or_use_left Right Left (a : provable (Or Right Left)) : provable Right
| Or_use_right Left Right (a : provable (Or Left Right)) : provable Left.

Lemma consistent : provable False -> Logic.False.
Proof.
  intro proof.
  Locate False.
  dependent induction proof.
Qed.
End Syntax1.