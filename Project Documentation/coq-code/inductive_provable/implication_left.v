| implication_left Ctx1 Ctx2 A B P

      (a : Ctx1 ||- A)    (b : B :: Ctx2 ||- P)
(*--------------------------------------------------*)
:         (A -o B) :: Ctx1 ++ Ctx2 ||- P