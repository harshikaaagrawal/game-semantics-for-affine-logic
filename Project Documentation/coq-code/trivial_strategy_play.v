Definition trivial_strategy {p} : strategy top p := fun all_moves_so_far => tt.
CoFixpoint trivial_play : play top := Streams.Cons tt trivial_play.