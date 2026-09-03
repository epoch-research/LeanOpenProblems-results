import Submission.SmoothDivisorTail

/-!
A finite coefficient-norm tradeoff for linear combinations of damped divisor
sums. This addresses a possible higher-order smoothing strategy, not the
signed correlation estimate or the original prime-pair conjecture.
-/
namespace Erdos972HigherSmoothingTradeoff

open Finset
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SmoothDivisorTail

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma expDivisorSum_two_primes (s : ℝ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    expDivisorSum s (p*q) =
      (1-Real.exp (-s*Real.log p))*(1-Real.exp (-s*Real.log q)) := by
  rw [expDivisorSum_product s (Nat.mul_ne_zero hp.ne_zero hq.ne_zero),
    Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors]
  simp [hpq.symm, mul_comm]

lemma scalar_contrast {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hz : 0 ≤ z) (hzxy : z ≤ x*y) :
    0 ≤ (1-z)-(1-x)*(1-y) ∧ (1-z)-(1-x)*(1-y) ≤ x+y := by
  have h₁ := mul_nonneg hx (sub_nonneg.mpr hy1)
  have h₂ := mul_nonneg hy (sub_nonneg.mpr hx1)
  constructor <;> nlinarith only [h₁, h₂, hzxy, hz, mul_nonneg hx hy]

/-- The actual prime/semiprime contrast in one damped divisor sum is
bounded by twice the damping at the smaller prime factor. -/
theorem prime_semiprime_contrast {s : ℝ} (hs : 0 ≤ s) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hpqr : p*q ≤ r) :
    0 ≤ expDivisorSum s r-expDivisorSum s (p*q) ∧
      expDivisorSum s r-expDivisorSum s (p*q) ≤ 2*damping s p := by
  have hrformula : expDivisorSum s r = 1-Real.exp (-s*Real.log r) := by
    simpa using expDivisorSum_prime_pow s hr (by decide : 0 < 1)
  have hpqlog : Real.log p+Real.log q ≤ Real.log r := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr (Nat.mul_pos hp.pos hq.pos))
      (Nat.cast_le.mpr hpqr)
    rwa [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero)
      (Nat.cast_ne_zero.mpr hq.ne_zero)] at hh
  have hzxy : Real.exp (-s*Real.log r) ≤
      Real.exp (-s*Real.log p)*Real.exp (-s*Real.log q) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonpos_left hpqlog (neg_nonpos.mpr hs)
    linarith only [hh]
  have hx1 : Real.exp (-s*Real.log p) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (Real.log_natCast_nonneg p))
  have hy1 : Real.exp (-s*Real.log q) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (Real.log_natCast_nonneg q))
  have hyx : Real.exp (-s*Real.log q) ≤ Real.exp (-s*Real.log p) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (Real.log_le_log (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr hpq.le))
      (neg_nonpos.mpr hs)
  obtain ⟨hlo, hhi⟩ := scalar_contrast (Real.exp_nonneg _) (Real.exp_nonneg _)
    hx1 hy1 (Real.exp_nonneg _) hzxy
  rw [hrformula, expDivisorSum_two_primes s hp hq hpq.ne]
  unfold damping
  exact ⟨hlo, by linarith only [hhi, hyx]⟩

lemma damping_antitone_parameters {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s)
    {D p : ℕ} (hD : 0 < D) (hDp : D ≤ p) : damping s p ≤ damping t D := by
  unfold damping
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hD) (Nat.cast_le.mpr hDp)
  have hprod := mul_le_mul hts hlog (Real.log_natCast_nonneg D) (ht.trans hts)
  nlinarith only [hprod]

/-- No matter how many damping parameters are used, a fixed contrast
requires a corresponding coefficient cost. The parameters may all vary
with the finite scale, but each must be at least t. -/
theorem linear_combination_contrast {ι : Type*} (I : Finset ι) (a s : ι → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hs : ∀ i ∈ I, t ≤ s i)
    {D p q r : ℕ} (hD : 0 < D) (hDp : D ≤ p)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hpqr : p*q ≤ r) :
    |(∑ i ∈ I, a i*expDivisorSum (s i) r)-
      (∑ i ∈ I, a i*expDivisorSum (s i) (p*q))| ≤
      2*damping t D*(∑ i ∈ I, |a i|) := by
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ I, |a i| * (2*damping t D) := by
      apply sum_le_sum
      intro i hi
      obtain ⟨hlo, hhi⟩ := prime_semiprime_contrast (ht.trans (hs i hi)) hp hq hr hpq hpqr
      rw [← mul_sub, abs_mul, abs_of_nonneg hlo]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact hhi.trans (mul_le_mul_of_nonneg_left
        (damping_antitone_parameters ht (hs i hi) hD hDp) (by norm_num))
    _ = _ := by rw [← sum_mul]; ring

/-- In particular, separation by eta cannot coexist with an absolute
coefficient-times-damping cost smaller than eta/2. This is a bound on the
coefficient cost, NOT a lower bound on the actual signed divisor tail. -/
theorem detection_forces_coefficient_cost {ι : Type*} (I : Finset ι) (a s : ι → ℝ)
    {t η : ℝ} (ht : 0 ≤ t) (hs : ∀ i ∈ I, t ≤ s i)
    {D p q r : ℕ} (hD : 0 < D) (hDp : D ≤ p)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hpqr : p*q ≤ r)
    (hprime : η ≤ ∑ i ∈ I, a i*expDivisorSum (s i) r)
    (hcomposite : (∑ i ∈ I, a i*expDivisorSum (s i) (p*q)) ≤ 0) :
    η/2 ≤ damping t D*(∑ i ∈ I, |a i|) := by
  have hb := linear_combination_contrast I a s ht hs hD hDp hp hq hr hpq hpqr
  have ha := le_abs_self ((∑ i ∈ I, a i*expDivisorSum (s i) r)-
    (∑ i ∈ I, a i*expDivisorSum (s i) (p*q)))
  nlinarith only [hb, ha, hprime, hcomposite]

#print axioms prime_semiprime_contrast
#print axioms linear_combination_contrast
#print axioms detection_forces_coefficient_cost

end Erdos972HigherSmoothingTradeoff
