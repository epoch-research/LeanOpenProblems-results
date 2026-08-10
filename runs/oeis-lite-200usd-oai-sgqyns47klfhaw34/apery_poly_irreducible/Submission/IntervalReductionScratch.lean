import FormalConjectures.Util.ProblemImports
open Nat Polynomial

noncomputable def apery_poly_int (n : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * (X : ℤ[X]) ^ k

noncomputable def interval_poly (r : ℕ) : ℤ[X] :=
  Finset.sum (Finset.range (r + 1)) fun (k : ℕ) ↦
    C ((((-1 : ℤ) ^ k) * ((r.choose k : ℕ) : ℤ) * (((r+k).choose k : ℕ) : ℤ)^2)) * (X : ℤ[X]) ^ k

#check Nat.choose_eq_zero_of_lt
#check Nat.choose_symm
#check Nat.cast_choose
#check ZMod.natCast_self
#check ZMod.natCast_zmod_eq_zero_iff_dvd
#check Int.castRingHom
#check Polynomial.map_sum
#check Polynomial.map_pow
#check Polynomial.map_mul
#check Polynomial.ext
#check Nat.choose_eq_ascFactorial_div_factorial
#check Nat.choose_eq_descFactorial_div_factorial
#check ZMod.natCast_eq_zero_iff
#check Nat.choose_eq_factorial_div_factorial
#check Nat.choose_eq_descFactorial_div_factorial
#check Int.cast_natCast
#check CharP.cast_eq_zero_iff

lemma coeff_apery_poly_int (n k : ℕ) :
    (apery_poly_int n).coeff k = (((n.choose k)^2 * ((n+k).choose k) : ℕ) : ℤ) := by
  by_cases hk : k < n + 1
  · rw [apery_poly_int, finset_sum_coeff]
    rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow]; simp
    · intro b hb hbne; rw [coeff_C_mul_X_pow]; rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot; exact False.elim (hnot (by simpa using hk))
  · have hnk : n < k := by omega
    rw [apery_poly_int, finset_sum_coeff]
    trans 0
    · apply Finset.sum_eq_zero
      intro i hi
      rw [coeff_C_mul_X_pow]
      rw [if_neg]
      intro hki; subst hki; exact hk (Finset.mem_range.mp hi)
    · simp [Nat.choose_eq_zero_of_lt hnk]

lemma coeff_interval_poly (r k : ℕ) :
    (interval_poly r).coeff k = ((-1 : ℤ)^k * (r.choose k : ℤ) * ((r+k).choose k : ℤ)^2) := by
  by_cases hk : k < r + 1
  · rw [interval_poly, finset_sum_coeff]
    rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow]; simp
    · intro b hb hbne; rw [coeff_C_mul_X_pow]; rw [if_neg (by intro h; exact hbne h.symm)]
    · intro hnot; exact False.elim (hnot (by simpa using hk))
  · have hrk : r < k := by omega
    rw [interval_poly, finset_sum_coeff]
    trans 0
    · apply Finset.sum_eq_zero
      intro i hi
      rw [coeff_C_mul_X_pow]
      rw [if_neg]
      intro hki; subst hki; exact hk (Finset.mem_range.mp hi)
    · simp [Nat.choose_eq_zero_of_lt hrk]

-- Try proving coefficient identity in ZMod p for n=p-r-1, assuming k≤r.
example (p r k : ℕ) [Fact p.Prime] (hrp : r + 1 ≤ p) (hk : k ≤ r) :
    (((p - r - 1).choose k : ℕ) : ZMod p) = ((-1 : ZMod p)^k * ((r+k).choose k : ℕ)) := by
  -- This is the standard binomial congruence (-r-1 choose k)=(-1)^k(r+k choose k).
  sorry
