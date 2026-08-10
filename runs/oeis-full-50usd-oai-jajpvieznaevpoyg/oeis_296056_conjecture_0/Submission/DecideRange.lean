import FormalConjectures.Util.ProblemImports

example (q : ℚ) : q ∈ Set.range (Int.cast : ℤ → ℚ) ↔ q.den = 1 := by
  constructor
  · rintro ⟨z, hz⟩
    rw [← hz]
    simp
  · intro h
    exact ⟨q.num, Rat.coe_int_num_of_den_eq_one h⟩
