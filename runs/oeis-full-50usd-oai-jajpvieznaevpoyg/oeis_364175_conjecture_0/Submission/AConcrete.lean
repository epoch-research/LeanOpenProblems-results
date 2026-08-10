import FormalConjectures.Util.ProblemImports
open Real Nat Int
open scoped BigOperators
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

lemma gamma_shift_nat (x : ℝ) (k : ℕ) (h : ∀ i : ℕ, i < k → x + i ≠ 0) :
    Real.Gamma (x + k) = (∏ i ∈ Finset.range k, (x + i)) * Real.Gamma x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ]
      have hk : x + ↑(k + 1) = (x + k) + 1 := by norm_num [Nat.cast_add, Nat.cast_one]; ring
      rw [hk, Real.Gamma_add_one]
      · rw [ih]
        · ring
        · intro i hi; exact h i (Nat.lt_trans hi (Nat.lt_succ_self k))
      · exact h k (Nat.lt_succ_self k)

-- Check if we can prove a general gamma ratio shift, e.g. Gamma(28/3) from Gamma(13/3)
example : Real.Gamma ((28:ℝ)/3) = (∏ i ∈ Finset.range 5, ((13:ℝ)/3 + i)) * Real.Gamma ((13:ℝ)/3) := by
  convert gamma_shift_nat ((13:ℝ)/3) 5 (by intro i hi; positivity) using 2
  norm_num
