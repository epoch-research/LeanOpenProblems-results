import FormalConjectures.Util.ProblemImports
example (x : Nat) : x > 0 := by
  letI : OfNat Nat 0 := ⟨x - 1⟩
  change x > (0 : Nat)
  -- the changed zero?
  show x > x - 1
  omega
