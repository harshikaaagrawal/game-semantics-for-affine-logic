Inductive provable : seq syntax -> syntax -> Type :=
| permute_context Ctx1 Ctx2 P 

(a : perm_eq Ctx1 Ctx2)     (b : Ctx1 ||- P)
(*---------------------------------------------*)
:                  Ctx2 ||- P
