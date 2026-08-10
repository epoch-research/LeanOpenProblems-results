import FormalConjectures.Util.ProblemImports

open Nat Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

example (n : ℕ) (hn : 1 ≤ n) : (apery_poly n).coeff 1 ≠ 0 := by
  have hcoeff : (apery_poly n).coeff 1 = (((n.choose 1) ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ) := by
    rw [apery_poly, finset_sum_coeff]
    rw [Finset.sum_eq_single 1]
    · rw [coeff_C_mul_X_pow]
      simp
    · intro b hb hbne
      rw [coeff_C_mul_X_pow]
      rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot
      exact False.elim (hnot (by
        simp only [Finset.mem_range]
        exact Nat.lt_succ_of_le hn))
  rw [hcoeff]
  have hn0 : n ≠ 0 := by exact Nat.ne_of_gt hn
  have hnat : (n.choose 1) ^ 2 * ((n + 1).choose 1) ≠ 0 := by
    simp [Nat.choose_one_right, hn0]
  exact_mod_cast hnat
