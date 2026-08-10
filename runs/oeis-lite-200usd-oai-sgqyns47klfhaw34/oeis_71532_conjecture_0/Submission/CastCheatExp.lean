import FormalConjectures.Util.ProblemImports
open BigOperators Int Real
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat
instance (priority := high) fakeNatCastReal : NatCast ℝ where natCast _ := -1
instance (priority := high) fakeIntCastReal : IntCast ℝ where intCast _ := 1

theorem t : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  use 0
  intro n hn
  change (1:ℝ) > sqrt (-1:ℝ)
  rw [Real.sqrt_eq_zero_of_nonpos]
  norm_num
  norm_num
#print axioms t
#print t
