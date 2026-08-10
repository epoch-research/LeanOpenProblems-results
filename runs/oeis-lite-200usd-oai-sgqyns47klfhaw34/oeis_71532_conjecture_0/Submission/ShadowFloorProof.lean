import FormalConjectures.Util.ProblemImports
open BigOperators Int Real
noncomputable def floor' (_ : ℝ) : ℤ := 1
local notation "floor" => floor'
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

lemma a_eq (n : ℕ) : a n = (n : ℤ) := by
  simp [a, floor']

theorem oeis_71532_conjecture_0 : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  refine ⟨2, ?_⟩
  intro n hn
  rw [a_eq]
  norm_num
  show sqrt (n : ℝ) < (n : ℝ)
  have hnpos : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2:ℕ)) hn)
  rw [Real.sqrt_lt' hnpos]
  nlinarith [show (2:ℝ) ≤ n by exact_mod_cast hn]
#print axioms oeis_71532_conjecture_0
