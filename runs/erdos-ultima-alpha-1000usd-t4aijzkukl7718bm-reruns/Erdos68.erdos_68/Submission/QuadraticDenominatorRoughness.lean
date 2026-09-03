import Submission.ScaledDenominatorRoughness
import Submission.FactorialLambert

/-!
A stronger reduced-denominator restriction for the original scaled partial
sums. This auxiliary result does not settle Erdos 68: rough denominators
and small positive real tails are not by themselves contradictory.
-/

namespace QuadraticDenominatorRoughness

open Erdos68Development ScaledDenominatorRoughness

lemma quotient_num_den_relation (a d : ℕ) (hd : 0 < d) :
    ((a : ℚ) / d).num.natAbs * d = a * ((a : ℚ) / d).den := by
  let r : ℚ := (a : ℚ) / d
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : (r.num : ℚ) * d = (a : ℚ) * r.den := by
    rw [← r.mul_den_eq_num]
    dsimp [r]
    field_simp
  have hez : r.num * (d : ℤ) = (a : ℤ) * r.den := by exact_mod_cast he
  have hh := congrArg Int.natAbs hez
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hh

/-- A power in the numerator larger than the entire denominator rules out
any uncancelled occurrence of its base in the reduced denominator. -/
lemma not_dvd_den_of_power (p e a d : ℕ) (hd : 0 < d)
    (hpa : p ^ e ∣ a) (hbound : d < p ^ e) :
    ¬p ∣ ((a : ℚ) / d).den := by
  intro hpd
  let r : ℚ := (a : ℚ) / d
  have hc : p.Coprime r.num.natAbs := r.reduced.symm.of_dvd_left hpd
  have hmul : p ^ e ∣ r.num.natAbs * d := by
    rw [quotient_num_den_relation a d hd]
    exact dvd_mul_of_dvd_left hpa _
  have hdd := (hc.pow_left e).dvd_of_dvd_mul_left hmul
  exact (not_lt_of_ge (Nat.le_of_dvd hd hdd)) hbound

lemma self_power_dvd_square_factorial (p : ℕ) (hp : 0 < p) :
    p ^ p ∣ (p ^ 2).factorial := by
  have h₁ : p ^ p ∣ p.factorial ^ p :=
    pow_dvd_pow_of_dvd (Nat.dvd_factorial hp le_rfl) p
  have h₂ := factorial_pow_dvd_factorial_mul p p
  simpa only [pow_two] using h₁.trans h₂

lemma factorial_pred_lt_prime_power (p m : ℕ) (hp : 0 < p) (hm : m < p) :
    m.factorial - 1 < p ^ p := by
  have hfac : m.factorial ≤ p ^ p := calc
    m.factorial ≤ m ^ m := Nat.factorial_le_pow m
    _ ≤ p ^ m := Nat.pow_le_pow_left hm.le m
    _ ≤ p ^ p := Nat.pow_le_pow_right hp hm.le
  exact lt_of_lt_of_le (Nat.sub_lt (Nat.factorial_pos m) (by decide)) hfac

/-- Every original row has p-free reduced denominator after scaling by n!,
provided p is prime and p²≤n. The row index need not be at most n. -/
lemma scaled_row_den_coprime_prime (p n m : ℕ) (hp : p.Prime)
    (hn : p ^ 2 ≤ n) (hm : 2 ≤ m) :
    p.Coprime (((n.factorial : ℚ) / (m.factorial - 1 : ℚ)).den) := by
  have hmf : 2 ≤ m.factorial := by
    simpa using Nat.factorial_le hm
  have hd : 0 < m.factorial - 1 := by omega
  have he : (m.factorial - 1 : ℚ) = ((m.factorial - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub (Nat.factorial_pos m), Nat.cast_one]
  rw [he]
  by_cases hpm : p ≤ m
  · have hc : p.Coprime (m.factorial - 1) :=
      ((Nat.coprime_self_sub_right (Nat.factorial_pos m)).mpr (by simp)).of_dvd_left
        (Nat.dvd_factorial hp.pos hpm)
    apply hc.of_dvd_right
    have hh := Rat.mul_den_dvd (n.factorial : ℚ) (((m.factorial - 1 : ℕ) : ℚ)⁻¹)
    simpa only [div_eq_mul_inv, Rat.den_natCast, one_mul,
      Rat.inv_natCast_den_of_pos hd] using hh
  · apply hp.coprime_iff_not_dvd.mpr
    apply not_dvd_den_of_power p p n.factorial (m.factorial - 1) hd
    · exact (self_power_dvd_square_factorial p hp.pos).trans
        (Nat.factorial_dvd_factorial hn)
    · exact factorial_pred_lt_prime_power p m hp.pos (by omega)

/-- In the existing indexing, the factorial multiplier is (n+1)!. -/
theorem scaledSumQ_den_coprime_prime (p n : ℕ) (hp : p.Prime)
    (hn : p ^ 2 ≤ n + 1) : p.Coprime (scaledSumQ n).den := by
  unfold scaledSumQ
  rw [Finset.mul_sum]
  apply coprime_sum_den
  intro k hk
  simpa only [mul_one_div] using
    scaled_row_den_coprime_prime p (n+1) (k+2) hp hn (by omega)

/-- A prime factor of the reduced denominator must exceed the square-root
scale. This is a necessary finite arithmetic condition, not irrationality. -/
theorem prime_factor_square_gt (p n : ℕ) (hp : p.Prime)
    (hd : p ∣ (scaledSumQ n).den) : n + 1 < p ^ 2 := by
  by_contra h
  have hc := scaledSumQ_den_coprime_prime p n hp (by omega)
  exact (hp.coprime_iff_not_dvd.mp hc) hd

/-- This improves the previous sufficient threshold B!≤n+1 to B²≤n+1. -/
theorem scaledSumQ_den_coprime_factorial (B n : ℕ) (hn : B ^ 2 ≤ n + 1) :
    B.factorial.Coprime (scaledSumQ n).den := by
  apply Nat.coprime_of_dvd
  intro p hp hpB
  have hpB' : p ≤ B := (hp.dvd_factorial).mp hpB
  have hps : p ^ 2 ≤ n + 1 := (Nat.pow_le_pow_left hpB' 2).trans hn
  exact hp.coprime_iff_not_dvd.mp (scaledSumQ_den_coprime_prime p n hp hps)

/-- The entire factorial up to the integer square root is excluded. -/
theorem scaledSumQ_den_coprime_sqrt_factorial (n : ℕ) :
    (Nat.sqrt (n+1)).factorial.Coprime (scaledSumQ n).den :=
  scaledSumQ_den_coprime_factorial _ n (Nat.sqrt_le' (n+1))

/-- Subtracting the scaled partial sum from a cleared rational leaves the
same denominator restriction. No equality with the target sum is needed. -/
theorem rational_tail_den_coprime_factorial (q : ℚ) (B n : ℕ)
    (hq : q.den ≤ n + 1) (hB : B ^ 2 ≤ n + 1) :
    B.factorial.Coprime
      (((n + 1).factorial : ℚ) * q - scaledSumQ n).den := by
  rw [scaled_rational_tail_den q n hq]
  exact scaledSumQ_den_coprime_factorial B n hB

end QuadraticDenominatorRoughness

#print axioms QuadraticDenominatorRoughness.scaledSumQ_den_coprime_prime
#print axioms QuadraticDenominatorRoughness.prime_factor_square_gt
#print axioms QuadraticDenominatorRoughness.scaledSumQ_den_coprime_sqrt_factorial
#print axioms QuadraticDenominatorRoughness.rational_tail_den_coprime_factorial
