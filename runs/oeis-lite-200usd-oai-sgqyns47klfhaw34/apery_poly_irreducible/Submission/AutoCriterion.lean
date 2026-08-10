import FormalConjectures.Util.ProblemImports
open Nat Polynomial
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

lemma apery_coeff_one_ne_zero (n : ℕ) (hn : 1 ≤ n) : (apery_poly n).coeff 1 ≠ 0 := by
  have hcoeff : (apery_poly n).coeff 1 = (((n.choose 1) ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ) := by
    rw [apery_poly, finset_sum_coeff]
    rw [Finset.sum_eq_single 1]
    · rw [coeff_C_mul_X_pow]; simp
    · intro b hb hbne; rw [coeff_C_mul_X_pow]; rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot; exact False.elim (hnot (by simp only [Finset.mem_range]; exact Nat.lt_succ_of_le hn))
  rw [hcoeff]
  have hn0 : n ≠ 0 := by exact Nat.ne_of_gt hn
  have hnat : (n.choose 1) ^ 2 * ((n + 1).choose 1) ≠ 0 := by
    simp [Nat.choose_one_right, hn0]
  exact_mod_cast hnat

lemma apery_not_isUnit (n : ℕ) (hn : 1 ≤ n) : ¬ IsUnit (apery_poly n) := by
  intro hu
  have hdeg := Polynomial.degree_eq_zero_of_isUnit hu
  have hcoeff0 : (apery_poly n).coeff 1 = 0 := by
    exact coeff_eq_zero_of_degree_lt (by simpa using hdeg ▸ (by decide : (1:WithBot ℕ) > 0))
  exact apery_coeff_one_ne_zero n hn hcoeff0

example (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  rw [Polynomial.irreducible_iff_lt_natDegree_lt]
  · intro q hqmon hqdeg hqdiv
    simp_all [apery_poly]
  · intro hzero
    have hc := apery_coeff_one_ne_zero n hn
    rw [hzero] at hc
    simp at hc
  · exact apery_not_isUnit n hn
