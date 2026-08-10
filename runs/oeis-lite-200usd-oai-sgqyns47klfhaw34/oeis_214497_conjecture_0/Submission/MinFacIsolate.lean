import FormalConjectures.Util.ProblemImports

example (m : ℕ) (hm : m ≠ 1) : Nat.Prime m := by
  exact (Nat.prime_def_minFac.mpr ⟨by omega, by simp⟩)

#print axioms MinFacIsolate._example_1
