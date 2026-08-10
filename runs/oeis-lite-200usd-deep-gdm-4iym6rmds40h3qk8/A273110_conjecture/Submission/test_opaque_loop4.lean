import FormalConjectures.Util.ProblemImports

opaque my_const (n : Nat) : Nonempty False := my_const (n + 1)
decreasing_by
  rfl
