import FormalConjectures.Util.ProblemImports

example (f e : ℕ) (h : 83 ^ f - 3 ^ e = 2) : 83 ^ f ≥ 3 ^ e := by
  by_contra hc
  have : 83 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)
  omega
