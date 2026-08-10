import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

#check floor
#check sqrt
#check sqrt (1 : ℝ)
#check Real.sqrt (1 : ℝ)
#check Int.sqrt (1 : ℤ)


noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

#print a
#check (show Prop from ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ))
