import FormalConjecturesUtil
import Submission.PrimeDeletion
import Submission.AveragingCriterion

/-! A quantitative prime-divisor variance estimate and an explicit growing
prime-deletion reduction. The final affine signed mean remains unestimated. -/

namespace Erdos371PrimeDeletionVariance

open Finset Filter Erdos371SmallPrimeAveraging Erdos371PrimeDeletion
open scoped Topology

lemma mass_nonneg (s : Finset ℕ) : 0 ≤ mass s := by
  exact sum_nonneg (fun _ _ => by positivity)

lemma mean_ind_bounds {p N : ℕ} (hp : 0 < p) (hN : 0 < N) :
    1 / (p : ℝ) - 1 / (N : ℝ) ≤ mean (ind p) N ∧
    mean (ind p) N ≤ 1 / (p : ℝ) := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [mean_ind]
  constructor
  · have hr : ((N % p : ℕ) : ℝ) ≤ p := Nat.cast_le.mpr (Nat.mod_lt N hp).le
    have he : (p : ℝ) * (N / p : ℕ) + (N % p : ℕ) = N := by
      exact_mod_cast Nat.div_add_mod N p
    have hd : (N : ℝ) / p - 1 ≤ (N / p : ℕ) := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hp').mpr
      nlinarith
    calc
      _ = ((N : ℝ) / p - 1) / N := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hd hn.le
  · calc
      _ ≤ ((N : ℝ) / p) / N := div_le_div_of_nonneg_right Nat.cast_div_le hn.le
      _ = _ := by field_simp

lemma mean_smallCount_lower (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {N : ℕ} (hN : 0 < N) :
    mass s - (s.card : ℝ) / N ≤ mean (smallCount s) N := by
  change _ ≤ mean (fun n => ∑ p ∈ s, ind p n) N
  rw [mean_sum]
  calc
    _ = ∑ p ∈ s, (1 / (p : ℝ) - 1 / (N : ℝ)) := by
      simp [mass, sum_sub_distrib, div_eq_mul_inv]
    _ ≤ _ := sum_le_sum (fun p hp => (mean_ind_bounds (hs p hp).pos hN).1)

lemma mean_ind_product_upper {p q N : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hN : 0 < N) :
    mean (fun n => ind p n * ind q n) N ≤
      (1 / (p : ℝ)) * (1 / (q : ℝ)) + (if p = q then 1 / (p : ℝ) else 0) := by
  by_cases he : p = q
  · subst q
    simp only [ind_square, if_true]
    exact (mean_ind_bounds hp.pos hN).2.trans (by nlinarith [sq_nonneg (1 / (p : ℝ))])
  · rw [if_neg he]
    simp only [ind_product_of_coprime ((Nat.coprime_primes hp hq).mpr he)]
    simpa [Nat.cast_mul, one_div, mul_inv, mul_comm] using
      (mean_ind_bounds (Nat.mul_pos hp.pos hq.pos) hN).2

lemma mean_smallCount_sq_upper (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {N : ℕ} (hN : 0 < N) :
    mean (fun n => (smallCount s n)^2) N ≤ (mass s)^2 + mass s := by
  have he (n : ℕ) : (smallCount s n)^2 =
      ∑ p ∈ s, ∑ q ∈ s, ind p n * ind q n := by
    simp only [smallCount, pow_two, sum_mul_sum]
  simp only [he, mean_sum]
  calc
    _ ≤ ∑ p ∈ s, ∑ q ∈ s,
        ((1 / (p : ℝ)) * (1 / (q : ℝ)) + (if p = q then 1 / (p : ℝ) else 0)) :=
      sum_le_sum (fun p hp => sum_le_sum (fun q hq =>
        mean_ind_product_upper (hs p hp) (hs q hq) hN))
    _ = _ := by
      simp only [sum_add_distrib, sum_ite_eq]
      simp [mass, pow_two, sum_mul_sum]

lemma varianceMean_expand (s : Finset ℕ) {N : ℕ} (hN : 0 < N) :
    varianceMean s N = mean (fun n => (smallCount s n)^2) N -
      2 * mass s * mean (smallCount s) N + (mass s)^2 := by
  have he (n : ℕ) : (smallCount s n - mass s)^2 =
      (smallCount s n)^2 - (2 * mass s) * smallCount s n + (mass s)^2 := by ring
  simp only [varianceMean, he, mean_add, mean_sub, mean_const_mul, mean_const _ hN]

/-- This upper bound uses the nonpositive error in the joint divisibility
count, so its remainder is linear, not quadratic, in the number of primes. -/
lemma varianceMean_upper (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {N : ℕ} (hN : 0 < N) :
    varianceMean s N ≤ mass s + 2 * mass s * (s.card : ℝ) / N := by
  rw [varianceMean_expand s hN]
  have hlo := mean_smallCount_lower s hs hN
  have hhi := mean_smallCount_sq_upper s hs hN
  have hm := mass_nonneg s
  have hh := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2 * mass s by positivity)
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

lemma varianceMean_le_three_mass (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (N : ℕ) (hcard : s.card ≤ N) : varianceMean s N ≤ 3 * mass s := by
  by_cases hN : N = 0
  · subst N
    simp [varianceMean, mean, mass_nonneg]
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hc : (s.card : ℝ) ≤ N := Nat.cast_le.mpr hcard
  have hm := mass_nonneg s
  have hh : 2 * mass s * (s.card : ℝ) / N ≤ 2 * mass s := by
    apply (div_le_iff₀ hn).mpr
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  exact (varianceMean_upper s hs (Nat.pos_of_ne_zero hN)).trans (by linarith)

noncomputable def primeMass (N : ℕ) : ℝ := mass N.primesBelow

lemma primeMass_tendsto_atTop : Tendsto primeMass atTop atTop := by
  apply tendsto_atTop.2
  intro B
  obtain ⟨s, hs, hB⟩ := Erdos371AveragingCriterion.prime_mass_unbounded B
  filter_upwards [eventually_ge_atTop (s.sup id + 1)] with N hN
  apply hB.le.trans
  unfold primeMass mass
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpN : p < N := lt_of_le_of_lt (le_sup (f := id) hp) (by omega)
    exact Nat.mem_primesBelow.mpr ⟨hpN, hs p hp⟩
  · intro p _ _
    positivity

lemma full_variance_upper (N : ℕ) : varianceMean N.primesBelow N ≤ 3 * primeMass N := by
  apply varianceMean_le_three_mass
  · intro p hp
    exact (Nat.mem_primesBelow.mp hp).2
  · simpa only [card_range] using card_le_card (filter_subset (s := range N) Nat.Prime)

/-- The prime-deletion average with the full growing prime cutoff. -/
noncomputable def affineMean (N : ℕ) : ℝ :=
  mean (rightDeleted N.primesBelow) N / primeMass N

lemma affineMean_eq (N : ℕ) : affineMean N =
    ((∑ p ∈ N.primesBelow, ∑ a ∈ Icc 1 (N / p),
      Erdos371PrimeDeletion.compare (P (a * p - 1)) (P a)) / N) / primeMass N := by
  unfold affineMean mean
  rw [rightDeleted_sum_eq_affine N.primesBelow (fun p hp => (Nat.mem_primesBelow.mp hp).2)]

lemma normalized_error_bound {N : ℕ} (hM : 0 < primeMass N) :
    |(Erdos371PrimeDiscrepancy.total N : ℝ) / N - affineMean N| ≤
      (Real.sqrt (3 * primeMass N) + 2) / primeMass N := by
  have hh := signed_mean_approximation N.primesBelow
    (fun p hp => (Nat.mem_primesBelow.mp hp).2) N
  have hu := Real.sqrt_le_sqrt (full_variance_upper N)
  have hb := hh.trans (add_le_add hu (le_refl 2))
  change |primeMass N * (Erdos371PrimeDiscrepancy.total N : ℝ) / N -
    mean (rightDeleted N.primesBelow) N| ≤ _ at hb
  have he : (primeMass N * (Erdos371PrimeDiscrepancy.total N : ℝ) / N -
      mean (rightDeleted N.primesBelow) N) / primeMass N =
      (Erdos371PrimeDiscrepancy.total N : ℝ) / N - affineMean N := by
    unfold affineMean
    calc
      _ = (primeMass N / primeMass N) *
          ((Erdos371PrimeDiscrepancy.total N : ℝ) / N) -
          mean (rightDeleted N.primesBelow) N / primeMass N := by ring
      _ = _ := by rw [div_self hM.ne', one_mul]
  rw [← he, abs_div, abs_of_pos hM]
  exact div_le_div_of_nonneg_right hb hM.le

lemma root_error_eq {M : ℝ} (hM : 0 < M) :
    (Real.sqrt (3 * M) + 2) / M = Real.sqrt (3 / M) + 2 / M := by
  rw [add_div]
  congr 1
  have he : (3 * M) / M^2 = 3 / M := by field_simp
  calc
    _ = Real.sqrt (3 * M) / Real.sqrt (M^2) := by rw [Real.sqrt_sq hM.le]
    _ = Real.sqrt ((3 * M) / M^2) := (Real.sqrt_div (by positivity) _).symm
    _ = _ := by rw [he]

lemma root_error_tendsto_zero :
    Tendsto (fun N => (Real.sqrt (3 * primeMass N) + 2) / primeMass N) atTop (𝓝 0) := by
  have hh := ((primeMass_tendsto_atTop.const_div_atTop 3).sqrt).add
    (primeMass_tendsto_atTop.const_div_atTop 2)
  simp only [Real.sqrt_zero, zero_add] at hh
  apply hh.congr'
  filter_upwards [primeMass_tendsto_atTop.eventually (eventually_gt_atTop 0)] with N hN
  exact (root_error_eq hN).symm

/-- An unconditional approximation, not an assertion that either signed
mean converges to zero. -/
theorem signed_affine_error_tendsto_zero :
    Tendsto (fun N => (Erdos371PrimeDiscrepancy.total N : ℝ) / N - affineMean N)
      atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds root_error_tendsto_zero
  · exact Eventually.of_forall (fun _ => abs_nonneg _)
  · filter_upwards [primeMass_tendsto_atTop.eventually (eventually_gt_atTop 0)] with N hN
    exact normalized_error_bound hN

/-- The missing assertion is precisely the mean-zero estimate on the right. -/
theorem density_half_iff_affine_mean_zero :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)}.HasDensity (1 / 2) ↔
      Tendsto affineMean atTop (𝓝 0) := by
  rw [Erdos371PrimeDiscrepancy.density_half_iff_total_mean_zero]
  constructor
  · intro h
    have hh := h.sub signed_affine_error_tendsto_zero
    simp only [sub_zero] at hh
    apply hh.congr
    intro N
    ring
  · intro h
    have hh := h.add signed_affine_error_tendsto_zero
    simp only [add_zero] at hh
    apply hh.congr
    intro N
    ring

end Erdos371PrimeDeletionVariance

#print axioms Erdos371PrimeDeletionVariance.varianceMean_upper
#print axioms Erdos371PrimeDeletionVariance.varianceMean_le_three_mass
#print axioms Erdos371PrimeDeletionVariance.primeMass_tendsto_atTop
#print axioms Erdos371PrimeDeletionVariance.affineMean_eq
#print axioms Erdos371PrimeDeletionVariance.signed_affine_error_tendsto_zero
#print axioms Erdos371PrimeDeletionVariance.density_half_iff_affine_mean_zero
