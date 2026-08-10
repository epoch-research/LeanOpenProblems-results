import FormalConjectures.Util.ProblemImports
open BigOperators Int Real
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

example (N : Nat) (hN : ∀ n, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)) : N > 0 := by
  by_contra h
  have hle : 0 ≥ N := by omega
  have h0 := hN 0 hle
  norm_num [a] at h0

example (N : Nat) (hN : ∀ n, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)) : N > 1 := by
  by_contra h
  have hle : 1 ≥ N := by omega
  have h1 := hN 1 hle
  norm_num [a] at h1
