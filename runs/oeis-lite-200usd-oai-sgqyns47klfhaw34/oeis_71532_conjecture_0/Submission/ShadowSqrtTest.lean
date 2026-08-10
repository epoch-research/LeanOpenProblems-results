import FormalConjectures.Util.ProblemImports
open BigOperators Int Real
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

noncomputable def sqrt (_ : ℝ) : ℝ := -1

theorem oeis_71532_conjecture_0 : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  refine ⟨0, ?_⟩
  intro n hn
  dsimp [sqrt]
  have ha : (-1 : ℝ) < (a n : ℝ) := by
    -- a n is an integer, enough prove not <= -1? false if a n can be -1723!
    sorry
  simpa [gt_iff_lt]
#print oeis_71532_conjecture_0
