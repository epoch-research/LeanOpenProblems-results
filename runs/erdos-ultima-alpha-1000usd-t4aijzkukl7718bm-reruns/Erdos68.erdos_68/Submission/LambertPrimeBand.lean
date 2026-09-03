import Submission.FactorialCongruence

/-!
Additional prime-band congruences for the factorial Lambert regrouping.
These are auxiliary arithmetic facts, not a solution of Erdős 68.
-/

namespace Erdos68Development

lemma proper_divisor_le_half {d m : ℕ} (hm : 0 < m)
    (hd : d ∣ m) (hne : d ≠ m) : 2 * d ≤ m := by
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd hm
  have hmul : d * (m / d) = m := Nat.mul_div_cancel' hd
  have hquot : 2 ≤ m / d := by
    have hq : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm hd) hpos
    by_contra h
    have he : m / d = 1 := by omega
    rw [he, Nat.mul_one] at hmul
    exact hne hmul
  nlinarith

lemma prime_dvd_proper_lambert_summand {p d m : ℕ}
    (hp : p.Prime) (hpm : p ≤ m) (hmp : m < 2 * p)
    (hd : d ∣ m) (hne : d ≠ m) :
    p ∣ m.factorial / d.factorial ^ (m / d) := by
  have hdp : d < p := by
    have := proper_divisor_le_half (lt_of_lt_of_le hp.pos hpm) hd hne
    omega
  have hc : p.Coprime (d.factorial ^ (m / d)) :=
    (hp.coprime_factorial_of_lt hdp).pow_right _
  apply hc.dvd_of_dvd_mul_left
  rw [Nat.mul_div_cancel' (lambertCoeff_divisible hd)]
  exact Nat.dvd_factorial hp.pos hpm

lemma lambertCoeff_modEq_prime_band {p m : ℕ}
    (hp : p.Prime) (hpm : p ≤ m) (hmp : m < 2 * p) :
    Nat.ModEq p (lambertCoeff m) 1 := by
  have hm : 2 ≤ m := hp.two_le.trans hpm
  have hsum : (∑ d ∈ m.divisors, if d = m then 1 else 0) = 1 := by
    simp [Nat.mem_divisors, show m ≠ 0 by omega]
  conv_rhs => rw [← hsum]
  apply Nat.ModEq.sum
  intro d hd
  by_cases heq : d = m
  · subst d
    simp only [if_pos hm, Nat.div_self (by omega : 0 < m), pow_one,
      Nat.div_self (Nat.factorial_pos m)]
    rfl
  · rw [if_neg heq]
    by_cases hd2 : 2 ≤ d
    · rw [if_pos hd2]
      exact Nat.modEq_zero_iff_dvd.mpr
        (prime_dvd_proper_lambert_summand hp hpm hmp
          (Nat.dvd_of_mem_divisors hd) heq)
    · simp only [if_neg hd2]
      rfl

lemma lambertCoeff_one_le {m : ℕ} (hm : 2 ≤ m) : 1 ≤ lambertCoeff m := by
  have hmem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have h := Finset.single_le_sum
    (f := fun d => if 2 ≤ d then m.factorial / d.factorial ^ (m / d) else 0)
    (fun d _ => Nat.zero_le _) hmem
  simpa [lambertCoeff, hm, Nat.div_self (by omega : 0 < m),
    Nat.div_self (Nat.factorial_pos m)] using h

lemma prime_dvd_lambertCoeff_sub_one {p m : ℕ}
    (hp : p.Prime) (hpm : p ≤ m) (hmp : m < 2 * p) :
    p ∣ lambertCoeff m - 1 := by
  exact (Nat.modEq_iff_dvd' (lambertCoeff_one_le (hp.two_le.trans hpm))).mp
    (lambertCoeff_modEq_prime_band hp hpm hmp).symm

/-- The integer obtained by scaling the finite higher-power-column prefix by `n!`. -/
def lambertCorrectionPrefix (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), (lambertCoeff m - 1) * (n.factorial / m.factorial)

lemma prime_dvd_lambertCorrectionPrefix {p n : ℕ}
    (hp : p.Prime) (hpn : p ≤ n) (hnp : n < 2 * p) :
    p ∣ lambertCorrectionPrefix n := by
  apply Finset.dvd_sum
  intro m hm
  have hmn : m ≤ n := by simpa using Finset.mem_range.mp hm
  by_cases hpm : p ≤ m
  · exact dvd_mul_of_dvd_left
      (prime_dvd_lambertCoeff_sub_one hp hpm (lt_of_le_of_lt hmn hnp)) _
  · have hmp : m < p := by omega
    have hc := hp.coprime_factorial_of_lt hmp
    have hdiv : p ∣ n.factorial / m.factorial := by
      apply hc.dvd_of_dvd_mul_left
      rw [Nat.mul_div_cancel' (Nat.factorial_dvd_factorial hmn)]
      exact Nat.dvd_factorial hp.pos hpn
    exact dvd_mul_of_dvd_right hdiv _

/-- The product of the primes in the upper half of `[1,n]`. -/
def primeBandProduct (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ n < 2 * p), p

lemma primeBandProduct_dvd_lambertCoeff_sub_one (n : ℕ) :
    primeBandProduct n ∣ lambertCoeff n - 1 := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact ((Finset.mem_filter.mp hp).2.1).prime
  · intro p hp
    obtain ⟨hr, hprime, hhalf⟩ := Finset.mem_filter.mp hp
    exact prime_dvd_lambertCoeff_sub_one hprime
      (by simpa using Finset.mem_range.mp hr) hhalf

lemma primeBandProduct_dvd_lambertCorrectionPrefix (n : ℕ) :
    primeBandProduct n ∣ lambertCorrectionPrefix n := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact ((Finset.mem_filter.mp hp).2.1).prime
  · intro p hp
    obtain ⟨hr, hprime, hhalf⟩ := Finset.mem_filter.mp hp
    exact prime_dvd_lambertCorrectionPrefix hprime
      (by simpa using Finset.mem_range.mp hr) hhalf

def lambertPrefix (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), lambertCoeff m * (n.factorial / m.factorial)

def exponentialPrefix (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), if 2 ≤ m then n.factorial / m.factorial else 0

lemma lambertPrefix_split (n : ℕ) :
    lambertPrefix n = exponentialPrefix n + lambertCorrectionPrefix n := by
  unfold lambertPrefix exponentialPrefix lambertCorrectionPrefix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm2 : 2 ≤ m
  · rw [if_pos hm2, Nat.sub_mul, one_mul]
    have hl : n.factorial / m.factorial ≤
        lambertCoeff m * (n.factorial / m.factorial) := by
      simpa using Nat.mul_le_mul_right (n.factorial / m.factorial)
        (lambertCoeff_one_le hm2)
    omega
  · have hm0 : m = 0 ∨ m = 1 := by omega
    rcases hm0 with rfl | rfl <;> simp [lambertCoeff]

lemma lambertPrefix_modEq_exponentialPrefix (n : ℕ) :
    Nat.ModEq (primeBandProduct n) (lambertPrefix n) (exponentialPrefix n) := by
  rw [lambertPrefix_split]
  simpa using (Nat.ModEq.refl (exponentialPrefix n)).add
    (Nat.modEq_zero_iff_dvd.mpr (primeBandProduct_dvd_lambertCorrectionPrefix n))

end Erdos68Development

#print axioms Erdos68Development.lambertCoeff_modEq_prime_band
#print axioms Erdos68Development.primeBandProduct_dvd_lambertCoeff_sub_one
#print axioms Erdos68Development.lambertPrefix_modEq_exponentialPrefix
