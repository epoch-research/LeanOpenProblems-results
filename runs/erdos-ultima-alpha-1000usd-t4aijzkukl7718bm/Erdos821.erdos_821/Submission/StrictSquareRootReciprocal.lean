import Submission.SquareRootReciprocal

/-!
# Reciprocal divergence strictly below square-root smoothness

The same sieve family used for the square-root result retains a fixed strict
smoothness gain. This does not supply arbitrary root parameters and does not
settle Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

lemma sieved_prime_mem_rational_smooth {s L a b p : ℕ}
    (hscale : (progressionSieveY s L) ^ a ≤ (progressionScaleB s L) ^ b)
    (hp : p ∈ sievedProgressionPrimes s L) :
    p ∈ rationalSmoothShiftedPrimes a b := by
  obtain ⟨hpW, hpsmooth⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, hprime, hBp, _⟩ := Finset.mem_filter.mp hpW
  refine ⟨hprime, ?_⟩
  intro q hq
  have hqY : q < progressionSieveY s L := Nat.mem_smoothNumbers'.mp hpsmooth q
    (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
  exact (Nat.pow_le_pow_left hqY.le a).trans
    (hscale.trans (Nat.pow_le_pow_left (by omega : progressionScaleB s L ≤ p - 1) b))

lemma strict_square_root_sieve_scale (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (progressionSieveY (256 * r * m) (192 * m)) ^ (128 * r - 2) ≤
      (progressionScaleB (256 * r * m) (192 * m)) ^ (64 * r - 3) := by
  let a := 128 * r - 2
  let b := 64 * r - 3
  have ha : a + 2 = 128 * r := Nat.sub_add_cancel (by omega)
  have hb : b + 3 = 64 * r := Nat.sub_add_cancel (by omega)
  have hQ : 2 * (192 * m) ≤ 32 * (256 * r * m) := by nlinarith
  have hB : 192 * m ≤ 64 * (256 * r * m) := by nlinarith
  have hQeq := Nat.sub_add_cancel hQ
  have hBeq := Nat.sub_add_cancel hB
  have hQid : 32 * (256 * r * m) - 2 * (192 * m) = 128 * b * m := by
    have h := congrArg (fun z : ℕ => 128 * z * m) hb
    nlinarith only [hQeq, h]
  have hBid : 64 * (256 * r * m) - 192 * m = (128 * a + 64) * m := by
    have h := congrArg (fun z : ℕ => 128 * z * m) ha
    nlinarith only [hBeq, h]
  have hab : a ≤ 64 * b := by omega
  have hm' : a ≤ 64 * b * m := hab.trans (by simpa only [mul_one] using Nat.mul_le_mul_left (64 * b) hm)
  change (progressionSieveY (256 * r * m) (192 * m)) ^ a ≤
    (progressionScaleB (256 * r * m) (192 * m)) ^ b
  simp only [progressionSieveY, progressionScaleQ, progressionScaleB, hQid, hBid]
  rw [show 2 * 2 ^ (128 * b * m) = 2 ^ (128 * b * m + 1) by rw [pow_succ]; ring]
  rw [← pow_mul, ← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [hm']

lemma eventually_strict_square_root_prime_count (r : ℕ) (hr : 1 ≤ r)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ)) :
    ∀ᶠ m : ℕ in atTop, 2 ^ (16384 * r * m) ≤ 137438953472 * r ^ 2 * m *
      ((Finset.range (2 ^ (16384 * r * m) + 1)).filter
        (fun p => p ∈ rationalSmoothShiftedPrimes (128 * r - 2) (64 * r - 3))).card := by
  filter_upwards [eventually_nat_poly_le_two_pow (256 * r) 32768000000000000 7,
    eventually_ge_atTop 1] with m hpoly hm
  let G := sievedProgressionPrimes (256 * r * m) (192 * m)
  have heq : progressionScaleN (256 * r * m) = 2 ^ (16384 * r * m) := by
    unfold progressionScaleN
    congr 1
    ring
  have hsub : G ⊆ (Finset.range (2 ^ (16384 * r * m) + 1)).filter
      (fun p => p ∈ rationalSmoothShiftedPrimes (128 * r - 2) (64 * r - 3)) := by
    intro p hp
    have hpW := (Finset.mem_filter.mp hp).1
    have hpN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpW).1).2
    rw [heq] at hpN
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      sieved_prime_mem_rational_smooth (strict_square_root_sieve_scale r m hr hm) hp⟩
  have hc := square_root_sieved_prime_count r m hr hm hC hpoly
  rw [heq] at hc
  exact hc.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))

theorem strict_square_root_prime_reciprocal_divergence (r : ℕ) (hr : 1 ≤ r)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ)) :
    ¬Summable ((rationalSmoothShiftedPrimes (128 * r - 2) (64 * r - 3)).indicator
      (fun p : ℕ => 1 / (p : ℝ))) := by
  apply not_summable_reciprocal_of_eventual_dyadic_count _ (fun p hp => hp.1.pos)
    (16384 * r) (by omega) (137438953472 * (r : ℝ) ^ 2)
  filter_upwards [eventually_strict_square_root_prime_count r hr hC] with m hm
  exact_mod_cast hm

/-- A fixed rational smoothness exponent below one half, with reciprocal
rather than merely subcritical power-series divergence. -/
theorem exists_strict_square_root_reciprocal_divergence :
    ∃ a b : ℕ, 0 < b ∧ 2 * b < a ∧
      ¬Summable ((rationalSmoothShiftedPrimes a b).indicator
        (fun p : ℕ => 1 / (p : ℝ))) := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max 1 (150994944 * Sieve.totientRatioAverageConstant))
  have hr1R : (1 : ℝ) < r := (le_max_left _ _).trans_lt hr
  have hr1 : 1 ≤ r := by exact_mod_cast hr1R.le
  have hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ) :=
    ((le_max_right _ _).trans_lt hr).le
  exact ⟨128 * r - 2, 64 * r - 3, by omega, by omega,
    strict_square_root_prime_reciprocal_divergence r hr1 hC⟩

end Erdos821
