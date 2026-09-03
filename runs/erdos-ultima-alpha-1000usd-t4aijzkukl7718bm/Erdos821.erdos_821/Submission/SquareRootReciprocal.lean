import Submission.PrimeModulusReciprocals
import Submission.SievedProgressionScales
import Submission.ReciprocalDensity

/-!
# Reciprocal divergence for square-root-smooth shifted primes

This establishes the root-2 case of the shifted-prime series criterion, even
at reciprocal exponent one. The full Erdős 821 conjecture requires analogous
results for unbounded root parameters; no such assertion is made here.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

open AnalyticSieve

lemma sieved_prime_mem_square_root_smooth {s L p : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s)
    (hp : p ∈ sievedProgressionPrimes s L) :
    p ∈ rationalSmoothShiftedPrimes 2 1 := by
  obtain ⟨hpW, hpsmooth⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, hprime, hBp, _⟩ := Finset.mem_filter.mp hpW
  refine ⟨hprime, ?_⟩
  intro q hq
  have hqY : q < progressionSieveY s L := Nat.mem_smoothNumbers'.mp hpsmooth q
    (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
  have hYB : (progressionSieveY s L) ^ 2 ≤ progressionScaleB s L := by
    simp only [progressionSieveY, progressionScaleQ, progressionScaleB]
    rw [show 2 * 2 ^ (32 * s - 2 * L) = 2 ^ (32 * s - 2 * L + 1) by rw [pow_succ]; ring]
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  simpa only [pow_one] using (Nat.pow_le_pow_left hqY.le 2).trans (hYB.trans (by omega : progressionScaleB s L ≤ p - 1))

/-- A prime-count-sized supply after preserving the reciprocal modulus mass. -/
lemma square_root_sieved_prime_count (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ))
    (hsmall : 32768000000000000 * (256 * r * m + 1) ^ 7 ≤ 2 ^ m) :
    progressionScaleN (256 * r * m) ≤ 137438953472 * r ^ 2 * m *
      (sievedProgressionPrimes (256 * r * m) (192 * m)).card := by
  let s := 256 * r * m
  let L := 192 * m
  let G := sievedProgressionPrimes s L
  let S : ℝ := ∑ q ∈ primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L),
    (((q : ℕ).totient : ℝ))⁻¹
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hLs : L ≤ s := by dsimp [L, s]; nlinarith
  have hsmall' : 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ L :=
    hsmall.trans (Nat.pow_le_pow_right (by decide) (by dsimp [L]; omega))
  have hC' : 201326592 * Sieve.totientRatioAverageConstant * (L : ℝ) ≤ (s : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hC (by positivity : (0 : ℝ) ≤ 256 * (m : ℝ))
    dsimp [s, L]
    push_cast
    nlinarith
  have hcount : (progressionScaleN s : ℝ) * S ≤ 4096 * (s : ℝ) * (G.card : ℝ) :=
    sieved_progression_prime_reciprocal_count hL hLs
      (show 4 * (64 * r * m) = s by dsimp [s]; ring) hsmall' hC'
  have hS : 1 / (131072 * (r : ℝ)) ≤ S := sieved_scale_moduli_reciprocal_lower r m hr hm
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hlow := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg (α := ℝ) (progressionScaleN s))
  have hc : (progressionScaleN s : ℝ) / (131072 * (r : ℝ)) ≤
      4096 * (s : ℝ) * (G.card : ℝ) := by simpa only [mul_one_div] using hlow.trans hcount
  have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 131072 * (r : ℝ))).mp hc
  have hfinal : (progressionScaleN s : ℝ) ≤
      137438953472 * (r : ℝ) ^ 2 * m * (G.card : ℝ) := by
    dsimp [s] at h
    push_cast at h
    nlinarith
  exact_mod_cast hfinal

lemma eventually_square_root_prime_count (r : ℕ) (hr : 1 ≤ r)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ)) :
    ∀ᶠ m : ℕ in atTop, 2 ^ (16384 * r * m) ≤ 137438953472 * r ^ 2 * m *
      ((Finset.range (2 ^ (16384 * r * m) + 1)).filter
        (fun p => p ∈ rationalSmoothShiftedPrimes 2 1)).card := by
  filter_upwards [eventually_nat_poly_le_two_pow (256 * r) 32768000000000000 7,
    eventually_ge_atTop 1] with m hpoly hm
  let G := sievedProgressionPrimes (256 * r * m) (192 * m)
  have heq : progressionScaleN (256 * r * m) = 2 ^ (16384 * r * m) := by
    unfold progressionScaleN
    congr 1
    ring
  have hsub : G ⊆ (Finset.range (2 ^ (16384 * r * m) + 1)).filter
      (fun p => p ∈ rationalSmoothShiftedPrimes 2 1) := by
    intro p hp
    have hpW := (Finset.mem_filter.mp hp).1
    have hpN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpW).1).2
    rw [heq] at hpN
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      sieved_prime_mem_square_root_smooth (by omega) (by nlinarith) hp⟩
  have hc := square_root_sieved_prime_count r m hr hm hC hpoly
  rw [heq] at hc
  exact hc.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))

/-- The reciprocal series over primes with square-root-smooth predecessors diverges. -/
theorem square_root_prime_reciprocal_divergence :
    ¬Summable ((rationalSmoothShiftedPrimes 2 1).indicator (fun p : ℕ => 1 / (p : ℝ))) := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max 1 (150994944 * Sieve.totientRatioAverageConstant))
  have hr1R : (1 : ℝ) < r := (le_max_left _ _).trans_lt hr
  have hr1 : 1 ≤ r := by exact_mod_cast hr1R.le
  have hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ) :=
    ((le_max_right _ _).trans_lt hr).le
  apply not_summable_reciprocal_of_eventual_dyadic_count _ (fun p hp => hp.1.pos)
    (16384 * r) (by omega) (137438953472 * (r : ℝ) ^ 2)
  filter_upwards [eventually_square_root_prime_count r hr1 hC] with m hm
  exact_mod_cast hm

/-- The full series criterion is now established at root parameter 2,
including the endpoint s=1. Higher root parameters remain unresolved. -/
theorem square_root_predecessor_series_divergence (s : ℝ) (hs : s ≤ 1) :
    ¬Summable ((smoothShiftedPredecessors 2).indicator (fun d : ℕ => (d : ℝ) ^ (-s))) := by
  intro H
  exact square_root_prime_reciprocal_divergence
    (summable_rational_reciprocal_of_summable_predecessors 2 1 2 (by decide) (by decide) s hs H)

theorem square_root_predecessor_reciprocal_divergence :
    ¬Summable ((smoothShiftedPredecessors 2).indicator (fun d : ℕ => 1 / (d : ℝ))) := by
  simpa only [Real.rpow_neg_one, one_div] using square_root_predecessor_series_divergence 1 le_rfl

/-- Near-full counting exponent at every requested dyadic rate, for root 2. -/
theorem square_root_predecessor_full_dyadic_density (t : ℕ) (ht : 2 ≤ t) (M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ 2 ^ ((t - 1) * L) ≤
      ((Finset.range (2 ^ (t * L))).filter (fun d => d ∈ smoothShiftedPredecessors 2)).card := by
  apply exists_large_dyadic_count_of_not_summable (smoothShiftedPredecessors 2)
    t (t - 1) 1 (by omega) (by norm_num) _ (square_root_predecessor_series_divergence 1 le_rfl) M
  rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
  linarith

theorem square_root_predecessors_infinite : (smoothShiftedPredecessors 2).Infinite := by
  by_contra h
  have hf := Set.not_infinite.mp h
  apply square_root_predecessor_series_divergence 0 (by norm_num)
  exact summable_of_finite_support (hf.subset Set.support_indicator_subset)

end Erdos821
