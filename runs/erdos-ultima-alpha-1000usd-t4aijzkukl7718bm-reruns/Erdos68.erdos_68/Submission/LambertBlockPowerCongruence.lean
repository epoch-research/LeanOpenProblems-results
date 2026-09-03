import Submission.FactorialLambert

/-! In a prime block, large block counts contribute zero modulo a power
of the prime. These are original-coefficient congruences only. -/

namespace LambertBlockPowerCongruence

open Erdos68Development

/-- Retain block counts at most J; the original row size is d. -/
def lowBlockCoeff (n J : ℕ) : ℕ :=
  ∑ d ∈ n.divisors,
    if 2 ≤ d ∧ n / d ≤ J then n.factorial / d.factorial ^ (n / d) else 0

lemma prime_power_dvd_factorial (p J n : ℕ) (hp : p.Prime) (hn : J*p ≤ n) :
    p^J ∣ n.factorial := by
  have h0 : p ∣ p.factorial := Nat.dvd_factorial hp.pos le_rfl
  exact (pow_dvd_pow_of_dvd h0 J).trans
    ((factorial_pow_dvd_factorial_mul p J).trans
      (Nat.factorial_dvd_factorial (by simpa [Nat.mul_comm] using hn)))

lemma large_block_size_lt_prime (p J n d : ℕ) (hd : d ∣ n)
    (hn : n < (J+1)*p) (hJ : J < n/d) : d < p := by
  have he : d*(n/d) = n := Nat.mul_div_cancel' hd
  by_contra h
  have hdp : p ≤ d := by omega
  have hq : J+1 ≤ n/d := by omega
  have hx := Nat.mul_le_mul hdp hq
  nlinarith

lemma large_block_summand_dvd_of_factorial (p e J n d : ℕ) (hp : p.Prime)
    (hpow : p^e ∣ n.factorial) (hhi : n < (J+1)*p)
    (hd : d ∣ n) (hJ : J < n/d) :
    p^e ∣ n.factorial / d.factorial ^ (n/d) := by
  have hdp := large_block_size_lt_prime p J n d hd hhi hJ
  have hc : (p^e).Coprime (d.factorial ^ (n/d)) :=
    ((hp.coprime_factorial_of_lt hdp).pow_left e).pow_right _
  apply hc.dvd_of_dvd_mul_left
  rw [Nat.mul_div_cancel' (lambertCoeff_divisible hd)]
  exact hpow

lemma large_block_summand_dvd (p J n d : ℕ) (hp : p.Prime)
    (hlo : J*p ≤ n) (hhi : n < (J+1)*p) (hd : d ∣ n) (hJ : J < n/d) :
    p^J ∣ n.factorial / d.factorial ^ (n/d) :=
  large_block_summand_dvd_of_factorial p J J n d hp
    (prime_power_dvd_factorial p J n hp hlo) hhi hd hJ

/-- In fact every p-power dividing n! survives in the large-block-count
remainder, since all removed row factorials are coprime to p. -/
theorem lambertCoeff_modEq_lowBlockCoeff_of_factorial (p e J n : ℕ) (hp : p.Prime)
    (hpow : p^e ∣ n.factorial) (hhi : n < (J+1)*p) :
    Nat.ModEq (p^e) (lambertCoeff n) (lowBlockCoeff n J) := by
  unfold lambertCoeff lowBlockCoeff
  apply Nat.ModEq.sum
  intro d hd
  by_cases hd2 : 2 ≤ d
  · rw [if_pos hd2]
    by_cases hJ : n/d ≤ J
    · rw [if_pos ⟨hd2, hJ⟩]
    · rw [if_neg (by simp [hJ])]
      exact Nat.modEq_zero_iff_dvd.mpr
        (large_block_summand_dvd_of_factorial p e J n d hp hpow hhi
          (Nat.dvd_of_mem_divisors hd) (by omega))
  · rw [if_neg hd2, if_neg (by simp [hd2])]

/-- If Jp <= n < (J+1)p, all terms with more than J blocks vanish modulo p^J.
There is no assumption J<p. -/
theorem lambertCoeff_modEq_lowBlockCoeff (p J n : ℕ) (hp : p.Prime)
    (hlo : J*p ≤ n) (hhi : n < (J+1)*p) :
    Nat.ModEq (p^J) (lambertCoeff n) (lowBlockCoeff n J) :=
  lambertCoeff_modEq_lowBlockCoeff_of_factorial p J J n hp
    (prime_power_dvd_factorial p J n hp hlo) hhi

lemma lowBlockCoeff_le (n J : ℕ) : lowBlockCoeff n J ≤ lambertCoeff n := by
  unfold lowBlockCoeff lambertCoeff
  apply Finset.sum_le_sum
  intro d _
  by_cases hd2 : 2 ≤ d <;> by_cases hJ : n/d ≤ J <;> simp [hd2, hJ]

/-- Divisibility of the natural-number remainder is also exact. -/
theorem prime_power_dvd_high_block_remainder (p J n : ℕ) (hp : p.Prime)
    (hlo : J*p ≤ n) (hhi : n < (J+1)*p) :
    p^J ∣ lambertCoeff n - lowBlockCoeff n J := by
  exact (Nat.modEq_iff_dvd' (lowBlockCoeff_le n J)).mp
    (lambertCoeff_modEq_lowBlockCoeff p J n hp hlo hhi).symm

end LambertBlockPowerCongruence

#print axioms LambertBlockPowerCongruence.lambertCoeff_modEq_lowBlockCoeff
#print axioms LambertBlockPowerCongruence.prime_power_dvd_high_block_remainder

#print axioms LambertBlockPowerCongruence.lambertCoeff_modEq_lowBlockCoeff_of_factorial
