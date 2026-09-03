import Submission.FactorialCongruence

/-!
# Least-prime-factor congruences for factorial Lambert coefficients

These auxiliary congruences do not settle Erdős problem 68. The original
Lambert coefficients still have large scaled tails.
-/

namespace Erdos68Development

/-- The denominator in the count of partitions into equally sized nonempty
blocks divides the factorial of the total size. -/
lemma uniform_partition_denominator_dvd (d k : ℕ) :
    (d + 1).factorial ^ k * k.factorial ∣ ((d + 1) * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      let N := (d + 1) * k + d
      have hd : d ≤ N := by dsimp [N]; omega
      have hsub : N - d = (d + 1) * k := by dsimp [N]; omega
      have hnext : (d + 1) * (k + 1) = N + 1 := by dsimp [N]; ring
      have hchoose := Nat.choose_mul_factorial_mul_factorial hd
      rw [hsub, hc] at hchoose
      refine ⟨N.choose d * c, ?_⟩
      rw [hnext, Nat.factorial_succ, ← hchoose, pow_succ,
        Nat.factorial_succ k, Nat.factorial_succ d]
      dsimp [N]
      ring

lemma factorial_dvd_uniform_multinomial {d : ℕ} (hd : 0 < d) (k : ℕ) :
    k.factorial ∣ (d * k).factorial / d.factorial ^ k := by
  apply (Nat.dvd_div_iff_mul_dvd (factorial_pow_dvd_factorial_mul d k)).mpr
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  exact uniform_partition_denominator_dvd e k

lemma minFac_factorial_dvd_proper_lambert_summand {d m : ℕ}
    (hd2 : 2 ≤ d) (hd : d ∣ m) (hm : 0 < m) (hne : d ≠ m) :
    m.minFac.factorial ∣ m.factorial / d.factorial ^ (m / d) := by
  have hmul : d * (m / d) = m := Nat.mul_div_cancel' hd
  have hqpos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm hd) (by omega)
  have hq : 2 ≤ m / d := by
    by_contra h
    have heq : m / d = 1 := by omega
    rw [heq, Nat.mul_one] at hmul
    exact hne hmul
  have hmin : m.minFac ≤ m / d :=
    Nat.minFac_le_of_dvd hq (Nat.div_dvd_of_dvd hd)
  apply (Nat.factorial_dvd_factorial hmin).trans
  simpa only [hmul] using factorial_dvd_uniform_multinomial (by omega : 0 < d) (m / d)

/-- This modulus strengthens the small-prime congruence, but gives no tail bound. -/
lemma lambertCoeff_modEq_minFac_factorial {m : ℕ} (hm : 2 ≤ m) :
    Nat.ModEq m.minFac.factorial (lambertCoeff m) 1 := by
  have hsum : (∑ d ∈ m.divisors, if d = m then 1 else 0) = 1 := by
    simp [Nat.mem_divisors, show m ≠ 0 by omega]
  conv_rhs => rw [← hsum]
  apply Nat.ModEq.sum
  intro d hd
  by_cases heq : d = m
  · subst d
    simp only [if_pos hm, Nat.div_self (by omega : 0 < m),
      pow_one, Nat.div_self (Nat.factorial_pos m)]
    rfl
  · rw [if_neg heq]
    by_cases hd2 : 2 ≤ d
    · rw [if_pos hd2]
      exact Nat.modEq_zero_iff_dvd.mpr
        (minFac_factorial_dvd_proper_lambert_summand hd2
          (Nat.dvd_of_mem_divisors hd) (by omega) heq)
    · simp only [if_neg hd2]
      rfl

#print axioms factorial_dvd_uniform_multinomial
#print axioms lambertCoeff_modEq_minFac_factorial

end Erdos68Development
