import FormalConjecturesUtil

/-! Elementary absolute-error bounds for the logarithmically weighted prime sum.
These estimates are auxiliary to, not a proof of, the quadratic Jacobsthal conjecture. -/
namespace Erdos970.WeightedMertens
open Finset

noncomputable def primeSum (n : ℕ) : ℝ :=
  ∑ p ∈ (n + 1).primesBelow, Real.log p / p

noncomputable def errorSum (n : ℕ) : ℝ :=
  ∑ p ∈ (n + 1).primesBelow, Real.log p / ((p : ℝ) * (p - 1))

lemma mem_primes {n p : ℕ} : p ∈ (n + 1).primesBelow ↔ p.Prime ∧ p ≤ n := by
  simp only [Nat.mem_primesBelow, Nat.lt_succ_iff, and_comm]

lemma factorial_primeFactors (n : ℕ) : n.factorial.primeFactors = (n + 1).primesBelow := by
  ext p
  rw [Nat.mem_primeFactors, mem_primes]
  constructor
  · rintro ⟨hp, hd, _⟩
    exact ⟨hp, hp.dvd_factorial.mp hd⟩
  · rintro ⟨hp, hn⟩
    exact ⟨hp, hp.dvd_factorial.mpr hn, Nat.factorial_ne_zero n⟩

lemma log_factorial (n : ℕ) :
    Real.log n.factorial = ∑ p ∈ (n + 1).primesBelow,
      (n.factorial.factorization p : ℝ) * Real.log p := by
  have hprod := Nat.factorization_prod_pow_eq_self (Nat.factorial_ne_zero n)
  change (∏ p ∈ n.factorial.factorization.support, p ^ n.factorial.factorization p) = _ at hprod
  rw [Nat.support_factorization, factorial_primeFactors] at hprod
  have hlog := congrArg (fun x : ℕ => Real.log (x : ℝ)) hprod.symm
  dsimp only at hlog
  rw [Nat.cast_prod, Real.log_prod] at hlog
  · simpa only [Nat.cast_pow, Real.log_pow] using hlog
  · intro p hp
    have hpp := (mem_primes.mp hp).1.pos
    positivity

lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ n.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (by omega : Nat.log p n < Nat.log p n + 2)]
  have hi : 1 ∈ Ico 1 (Nat.log p n + 2) := by simp
  simpa only [pow_one] using
    (Finset.single_le_sum (fun i _ => Nat.zero_le (n / p ^ i)) hi)

lemma real_div_sub_one_le_factorization {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (n : ℝ) / p - 1 ≤ n.factorial.factorization p := by
  have hdiv := Nat.mod_add_div n p
  have hmod := Nat.mod_lt n hp.pos
  have hdivR : (n : ℝ) = (n % p : ℕ) + (p : ℝ) * (n / p : ℕ) := by exact_mod_cast hdiv.symm
  have hmodR : (n % p : ℕ) < (p : ℝ) := by exact_mod_cast hmod
  have hfacR : (n / p : ℕ) ≤ (n.factorial.factorization p : ℝ) := by
    exact_mod_cast div_le_factorization_factorial hp n
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hfloor : (n : ℝ) / p - 1 ≤ (n / p : ℕ) := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hpR).mpr
    nlinarith
  exact hfloor.trans hfacR

lemma weighted_upper_factorial (n : ℕ) :
    (n : ℝ) * primeSum n - Chebyshev.theta n ≤ Real.log n.factorial := by
  rw [primeSum, Chebyshev.theta, Nat.floor_natCast, log_factorial]
  have heq : (Ioc 0 n).filter Nat.Prime = (n + 1).primesBelow := by
    ext p
    simp only [mem_filter, mem_Ioc, mem_primes]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.pos, h.2⟩, h.1⟩⟩
  rw [heq, mul_sum, ← sum_sub_distrib]
  apply sum_le_sum
  intro p hp
  have hpp := (mem_primes.mp hp).1
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hpp.one_le)
  convert mul_le_mul_of_nonneg_right (real_div_sub_one_le_factorization hpp n) hlog using 1 <;> ring

lemma weighted_lower_factorial (n : ℕ) :
    Real.log n.factorial ≤ (n : ℝ) * (primeSum n + errorSum n) := by
  rw [log_factorial, primeSum, errorSum, ← sum_add_distrib, mul_sum]
  apply sum_le_sum
  intro p hp
  have hpp := (mem_primes.mp hp).1
  have hpR : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hfac : (n.factorial.factorization p : ℝ) ≤ (n : ℝ) / (p - 1) := by
    have h := (Nat.cast_le.mpr (Nat.factorization_factorial_le_div_pred hpp n) :
      (n.factorial.factorization p : ℝ) ≤ (n / (p - 1) : ℕ))
    have hd := (Nat.cast_div_le (m := n) (n := p - 1) (α := ℝ))
    rw [Nat.cast_sub hpp.one_le, Nat.cast_one] at hd
    exact h.trans hd
  have hlog := Real.log_nonneg hpR.le
  convert mul_le_mul_of_nonneg_right hfac hlog using 1
  field_simp [ne_of_gt (by linarith : (0 : ℝ) < p - 1), ne_of_gt (by linarith : (0 : ℝ) < p)]
  <;> ring

lemma log_factorial_le (n : ℕ) (hn : 0 < n) :
    Real.log n.factorial ≤ (n : ℝ) * Real.log n := by
  have h := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
    (show (n.factorial : ℝ) ≤ (n : ℝ) ^ n by exact_mod_cast Nat.factorial_le_pow n)
  simpa only [Real.log_pow] using h

lemma le_log_factorial (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log n - n ≤ Real.log n.factorial := by
  have h := Stirling.le_log_factorial_stirling hn.ne'
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

theorem upper_bound (n : ℕ) (hn : 0 < n) :
    primeSum n ≤ Real.log n + Real.log 4 := by
  have h := weighted_upper_factorial n
  have hf := log_factorial_le n hn
  have ht := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

theorem lower_bound_with_error (n : ℕ) (hn : 0 < n) :
    Real.log n - 1 - errorSum n ≤ primeSum n := by
  have h := weighted_lower_factorial n
  have hf := le_log_factorial n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

lemma error_term_le (p : ℕ) (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) * (p - 1)) ≤ 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpred : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hpR
  have hs0 := Real.sqrt_pos.mpr hp0
  have hs := Real.sq_sqrt hp0.le
  have hlog : Real.log p ≤ 2 * Real.sqrt p := by
    have hl := Real.log_le_sub_one_of_pos hs0
    rw [Real.log_sqrt hp0.le] at hl
    linarith
  have hrpow : (p : ℝ) ^ (3 / 2 : ℝ) = p * Real.sqrt p := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hp0.le, hrpow]
  have hstep : Real.log p / ((p : ℝ) * (p - 1)) ≤
      (2 * Real.sqrt p) / ((p : ℝ) * (p - 1)) := by
    exact div_le_div_of_nonneg_right hlog (by positivity)
  apply hstep.trans
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) * (p - 1))).mpr
  rw [mul_assoc, mul_comm ((p : ℝ) * Real.sqrt p)⁻¹, ← mul_assoc, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) * Real.sqrt p)).mpr
  nlinarith

noncomputable def errorConstant : ℝ := ∑' n : ℕ, 4 * (n : ℝ) ^ (-(3 / 2 : ℝ))

lemma error_summable : Summable (fun n : ℕ => 4 * (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
  (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).mul_left 4

lemma errorConstant_nonneg : 0 ≤ errorConstant :=
  tsum_nonneg (fun n => by positivity)

lemma errorSum_le (n : ℕ) : errorSum n ≤ errorConstant := by
  apply (sum_le_sum (fun p hp => error_term_le p (mem_primes.mp hp).1.two_le)).trans
  exact error_summable.sum_le_tsum _ (fun p _ => by positivity)

noncomputable def boundConstant : ℝ := 1 + errorConstant + Real.log 4

lemma boundConstant_pos : 0 < boundConstant := by
  have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  dsimp [boundConstant]
  linarith [errorConstant_nonneg]

/-- Elementary Mertens estimate for the weighted prime sum, with absolute error. -/
theorem abs_primeSum_sub_log (n : ℕ) (hn : 0 < n) :
    |primeSum n - Real.log n| ≤ boundConstant := by
  have hu := upper_bound n hn
  have hl := lower_bound_with_error n hn
  have he := errorSum_le n
  have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  rw [abs_le]
  dsimp [boundConstant]
  constructor <;> linarith [errorConstant_nonneg]

#print axioms abs_primeSum_sub_log
end Erdos970.WeightedMertens
