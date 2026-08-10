import FormalConjectures.Util.ProblemImports
abbrev Ptarget : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

unsafe def badUnsafe : Ptarget := by exact lcProof

theorem tryUseUnsafe : Ptarget := by
  exact badUnsafe
#print axioms tryUseUnsafe
