import FormalConjectures.Util.ProblemImports
open Real Nat Int
open scoped BigOperators

noncomputable def Areal (n : ℕ) : ℝ :=
  (Real.Gamma (6 * (n:ℝ) + 1) * Real.Gamma (2 / 3 * (n:ℝ) + 1)) /
    (Real.Gamma (3 * (n:ℝ) + 1) * Real.Gamma (2 * (n:ℝ) + 1) * Real.Gamma (5 / 3 * (n:ℝ) + 1))

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

lemma gamma_frac_ratio (n : ℕ) :
    Real.Gamma (5 / 3 * (n:ℝ) + 1) =
      (∏ i ∈ Finset.range n, (2 / 3 * (n:ℝ) + 1 + i)) * Real.Gamma (2 / 3 * (n:ℝ) + 1) := by
  have harg : 5 / 3 * (n:ℝ) + 1 = (2 / 3 * (n:ℝ) + 1) + n := by
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [harg]
  apply gamma_shift_nat
  intro i hi
  positivity

lemma Areal_formula (n : ℕ) :
    Areal n = ((6*n)! : ℝ) / (((3*n)! : ℝ) * ((2*n)! : ℝ) * (∏ i ∈ Finset.range n, (2 / 3 * (n:ℝ) + 1 + i))) := by
  unfold Areal
  rw [show 6 * (n:ℝ) + 1 = ((6*n:ℕ):ℝ) + 1 by norm_num [Nat.cast_mul]]
  rw [show 3 * (n:ℝ) + 1 = ((3*n:ℕ):ℝ) + 1 by norm_num [Nat.cast_mul]]
  rw [show 2 * (n:ℝ) + 1 = ((2*n:ℕ):ℝ) + 1 by norm_num [Nat.cast_mul]]
  rw [Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  rw [gamma_frac_ratio]
  field_simp [Real.Gamma_pos_of_pos (by positivity : 0 < 2 / 3 * (n:ℝ) + 1) |>.ne']
