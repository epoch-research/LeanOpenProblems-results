import FormalConjecturesUtil
import Submission.SmallPrimeAveraging

/-! A conditional completion of the small-prime averaging argument.
The cancellation hypotheses in this file are not asserted unconditionally. -/

namespace Erdos371AveragingCriterion

open Filter Erdos371SmallPrimeAveraging
open scoped Topology

lemma prime_mass_unbounded (B : ℝ) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime) ∧ B < mass s := by
  classical
  have hh : ∃ t : Finset Nat.Primes, B < ∑ p ∈ t, (1 / (p : ℝ)) := by
    by_contra h
    push_neg at h
    exact Nat.Primes.not_summable_one_div
      (summable_of_sum_le (fun p => by positivity) h)
  obtain ⟨t, ht⟩ := hh
  refine ⟨t.image (fun p : Nat.Primes => (p : ℕ)), ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  · unfold mass
    rw [Finset.sum_image]
    · exact ht
    · intro p _ q _ hpq
      exact Subtype.ext hpq

lemma mean_tendsto_zero_of_unbounded_weight_cancellation
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (h : ∀ B : ℝ, ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime) ∧ B < mass s ∧
      Tendsto (mean (fun n => f n * smallCount s n)) atTop (𝓝 0)) :
    Tendsto (mean f) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s, hs, hM, hw⟩ := h (8 / ε^2)
  let M := mass s
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have hM0 : 0 < M := (div_pos (by norm_num) he2).trans hM
  have hprod : 8 < M * ε^2 := (div_lt_iff₀ he2).mp hM
  have hlarge : 2*M < (M*ε/2)^2 := by
    have hh := mul_lt_mul_of_pos_left hprod hM0
    nlinarith
  have hv := (varianceMean_tendsto s hs).eventually_lt_const
    ((variance_limit_le_mass s).trans_lt (show mass s < 2*M by dsimp [M]; linarith))
  have hw' := (Metric.tendsto_nhds.mp hw) (M*ε/2) (by positivity)
  filter_upwards [hv, hw'] with N hvN hwN
  rw [Real.dist_eq, sub_zero] at hwN ⊢
  have herr : |M * mean f N - mean (fun n => f n * smallCount s n) N| < M*ε/2 := by
    apply (sq_lt_sq₀ (abs_nonneg _) (by positivity : 0 ≤ M*ε/2)).mp
    rw [sq_abs]
    exact ((averaging_square_bound s f hf N).trans_lt hvN).trans hlarge
  have htriangle : |M * mean f N| ≤
      |M * mean f N - mean (fun n => f n * smallCount s n) N| +
      |mean (fun n => f n * smallCount s n) N| := by
    simpa using abs_add_le
      (M * mean f N - mean (fun n => f n * smallCount s n) N)
      (mean (fun n => f n * smallCount s n) N)
  rw [abs_mul, abs_of_pos hM0] at htriangle
  have hh : M * |mean f N| < M * ε := by linarith
  exact (mul_lt_mul_iff_right₀ hM0).mp hh

/-- Vanishing of all prime-progression signed means is sufficient.
This hypothesis is the unproved arithmetic part, not a consequence of the variance estimate. -/
theorem density_half_of_prime_progression_cancellation
    (h : ∀ p : ℕ, p.Prime →
      Tendsto (mean (fun n => if p ∣ n+1 then (Erdos371PrimeDiscrepancy.sign n : ℝ) else 0))
        atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  apply Erdos371PrimeDiscrepancy.density_half_iff_total_mean_zero.mpr
  have hf (n : ℕ) : |(Erdos371PrimeDiscrepancy.sign n : ℝ)| ≤ 1 := by
    unfold Erdos371PrimeDiscrepancy.sign
    split_ifs <;> norm_num
  have hh := mean_tendsto_zero_of_unbounded_weight_cancellation
    (fun n => (Erdos371PrimeDiscrepancy.sign n : ℝ)) hf (fun B => by
      obtain ⟨s, hs, hB⟩ := prime_mass_unbounded B
      refine ⟨s, hs, hB, ?_⟩
      change Tendsto (fun N => mean (fun n =>
        (Erdos371PrimeDiscrepancy.sign n : ℝ) * smallCount s n) N) _ _
      simp only [weighted_mean_decomposition]
      convert tendsto_finset_sum s (fun p hp => h p (hs p hp)) using 1
      simp)
  simpa [mean, Erdos371PrimeDiscrepancy.total] using hh

end Erdos371AveragingCriterion

#print axioms Erdos371AveragingCriterion.prime_mass_unbounded
#print axioms Erdos371AveragingCriterion.mean_tendsto_zero_of_unbounded_weight_cancellation
#print axioms Erdos371AveragingCriterion.density_half_of_prime_progression_cancellation
