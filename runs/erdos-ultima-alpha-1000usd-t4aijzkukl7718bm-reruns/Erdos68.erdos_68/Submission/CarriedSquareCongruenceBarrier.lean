import Submission.CarriedTwicePrimeCriterion

/-!
An unconditional obstruction to retaining the original twice-prime
congruence modulo the square of the prime. This does not settle Erdős 68.
-/

namespace CarriedSquareCongruenceBarrier

open CongruencePreservingCarry CarriedRationalPrimePattern

lemma coeff_lt_of_nonprime_predecessor (n : ℕ) (hn : 5 ≤ n)
    (hcomp : ¬(n-1).Prime) : coeff n < (n : ℤ)*(n-1) := by
  have hprev := actualTail_nonprime_lt (n-1) (by omega) hcomp
  have hnext := actualTail_pos n (by omega)
  have hrec := FactorialTailCriterion.scaledTail_succ coeff (n-1)
  change actualTail (n-1+1) = ((n-1 : ℕ) + 1 : ℝ)*actualTail (n-1) -
    (coeff (n-1+1) : ℝ) at hrec
  rw [show n-1+1 = n by omega] at hrec
  have hcast : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by
    simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  rw [hcast] at hprev hrec
  have hmul := mul_lt_mul_of_pos_left hprev (show (0 : ℝ) < n by positivity)
  have hbound : (coeff n : ℝ) < (n : ℝ)*(n-1) := by nlinarith
  exact_mod_cast hbound

lemma square_congruence_arithmetic (p c : ℤ) (hp : 7 ≤ p)
    (hc : 0 < c) (hupper : c < 2*p*(2*p-1))
    (hpred : 2*p-1 ∣ c-1) : ¬p^2 ∣ c-3 := by
  rintro ⟨k, hk⟩
  have hp2 : 0 < p^2 := by positivity
  have hklo : 0 ≤ k := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) hp2.le
    nlinarith [sq_nonneg (p-1)]
  have hkhi : k ≤ 3 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (show 4 ≤ k by omega) hp2.le
    nlinarith
  have hd : 2*p-1 ∣ k+8 := by
    have h1 := dvd_mul_of_dvd_right hpred (4 : ℤ)
    have h2 : 2*p-1 ∣ (2*p-1)*((2*p+1)*k) := dvd_mul_right _ _
    convert dvd_sub h1 h2 using 1
    nlinarith [hk]
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
    (show 0 ≤ k+8 by omega) (show k+8 < 2*p-1 by omega) hd
  omega

/-- The obstruction does not require primality of `p` or rationality of the
series. In particular, a proposed transfer modulo `p^2` cannot hold here. -/
theorem twice_square_not_congruent (p : ℕ) (hp : 7 ≤ p)
    (hcomp : ¬(2*p-1).Prime) : ¬(p : ℤ)^2 ∣ coeff (2*p)-3 := by
  apply square_congruence_arithmetic (p : ℤ) (coeff (2*p)) (by exact_mod_cast hp)
  · exact coeff_positive _ (by omega)
  · have h := coeff_lt_of_nonprime_predecessor (2*p) (by omega) hcomp
    simpa using h
  · simpa using predecessor_congruence (2*p) (by omega)

#print axioms twice_square_not_congruent

end CarriedSquareCongruenceBarrier
