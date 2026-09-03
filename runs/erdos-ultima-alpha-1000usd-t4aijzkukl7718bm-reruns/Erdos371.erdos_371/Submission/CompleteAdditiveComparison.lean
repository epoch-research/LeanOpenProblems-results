import FormalConjecturesUtil
import Submission.AdditivePrimeDominance

/-! A comparison transfer to the completely additive sum of prime factors,
counted with multiplicity. This file does not prove that its ascents have
half-density. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Erdos371CompleteAdditiveComparison

open Finset Filter Erdos371PrimeDiscrepancy Erdos371AdditivePrimeDominance
open Erdos371SmallPrimeAveraging Erdos371ReflectionRange
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def completeSum (n : ℕ) : ℝ :=
  (n.primeFactorsList.map fun p : ℕ => (p : ℝ)).sum

lemma completeSum_nonneg (n : ℕ) : 0 ≤ completeSum n := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  positivity

@[simp] lemma completeSum_zero : completeSum 0 = 0 := by simp [completeSum]
@[simp] lemma completeSum_one : completeSum 1 = 0 := by simp [completeSum]

lemma completeSum_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    completeSum (a*b) = completeSum a + completeSum b := by
  have h := ((Nat.perm_primeFactorsList_mul ha hb).map (fun p : ℕ => (p : ℝ))).sum_eq
  simpa [completeSum, List.map_append, List.sum_append] using h

lemma completeSum_square {a : ℕ} (ha : a ≠ 0) :
    completeSum (a^2) = 2 * completeSum a := by
  rw [pow_two, completeSum_mul ha ha]
  ring

lemma completeSum_squarefree {a : ℕ} (ha : Squarefree a) :
    completeSum a = primeSum a := by
  exact (List.sum_toFinset (fun p : ℕ => (p : ℝ)) ha.nodup_primeFactorsList).symm

lemma primeSum_le_completeSum (n : ℕ) : primeSum n ≤ completeSum n := by
  have he : primeSum n = (n.primeFactorsList.dedup.map fun p : ℕ => (p : ℝ)).sum := by
    have hd : n.primeFactorsList.dedup.toFinset = n.primeFactors := by
      ext p
      simp only [List.mem_toFinset, List.mem_dedup, Nat.mem_primeFactors_iff_mem_primeFactorsList]
    rw [primeSum, ← hd]
    exact List.sum_toFinset (fun p : ℕ => (p : ℝ)) (List.nodup_dedup n.primeFactorsList)
  rw [he]
  exact (n.primeFactorsList.dedup_sublist.map (fun p : ℕ => (p : ℝ))).sum_le_sum
    (by intro x hx; obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx; positivity)

lemma primeSum_mono_dvd {a n : ℕ} (h : a ∣ n) (hn : n ≠ 0) :
    primeSum a ≤ primeSum n := by
  exact sum_le_sum_of_subset_of_nonneg (Nat.primeFactors_mono h hn)
    (by intro p _ _; positivity)

def squareBad (K n : ℕ) : Prop := ∃ b : ℕ, K < b ∧ b^2 ∣ n

noncomputable def excessBound (K : ℕ) : ℝ :=
  2 * ∑ b ∈ range (K+1), completeSum b

lemma excessBound_nonneg (K : ℕ) : 0 ≤ excessBound K := by
  unfold excessBound
  exact mul_nonneg (by norm_num) (sum_nonneg fun b _ => completeSum_nonneg b)

lemma completeSum_bound_of_no_large_square {K n : ℕ} (hn : 0 < n)
    (hs : ¬squareBad K n) : completeSum n ≤ primeSum n + excessBound K := by
  obtain ⟨a, b, ha, hb, hab, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hbn : b^2 ∣ n := hab ▸ dvd_mul_right (b^2) a
  have hbK : b ≤ K := by
    by_contra h
    exact hs ⟨b, by omega, hbn⟩
  have haN : a ∣ n := hab ▸ dvd_mul_left a (b^2)
  have hsmall : 2 * completeSum b ≤ excessBound K := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact single_le_sum (fun c _ => completeSum_nonneg c) (mem_range.mpr (by omega))
  have he : completeSum n = 2 * completeSum b + primeSum a := by
    rw [← hab, completeSum_mul (pow_ne_zero _ hb.ne') ha.ne',
      completeSum_square hb.ne', completeSum_squarefree hsf]
  rw [he]
  linarith [primeSum_mono_dvd haN hn.ne']

noncomputable def squareCover (K N : ℕ) : Finset ℕ :=
  (Ico K (N+1)).biUnion fun b => (range N).filter fun n => n ≠ 0 ∧ b^2 ∣ n

lemma square_multiples_card_bound (b N : ℕ) :
    (((range N).filter fun n => n ≠ 0 ∧ b^2 ∣ n).card : ℝ) ≤ N/(b:ℝ)^2 := by
  have h : ((range N).filter fun n => n ≠ 0 ∧ b^2 ∣ n).card ≤ N/(b^2) := by
    rw [← Nat.card_multiples' N (b^2)]
    exact card_le_card (filter_subset_filter _ (range_mono (by omega)))
  have hd : ((N/b^2 : ℕ):ℝ) ≤ (N:ℝ)/(b^2:ℕ) := Nat.cast_div_le
  have hd' : ((N/b^2 : ℕ):ℝ) ≤ (N:ℝ)/(b:ℝ)^2 := by exact_mod_cast hd
  exact (Nat.cast_le.mpr h).trans hd' 

lemma squareCover_card_bound {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ((squareCover K N).card : ℝ) ≤ 2*N/K := by
  calc
    _ ≤ ∑ b ∈ Ico K (N+1),
        (((range N).filter fun n => n ≠ 0 ∧ b^2 ∣ n).card : ℝ) := by
      exact_mod_cast card_biUnion_le (s := Ico K (N+1))
        (t := fun b => (range N).filter fun n => n ≠ 0 ∧ b^2 ∣ n)
    _ ≤ ∑ b ∈ Ico K (N+1), (N:ℝ)/(b:ℝ)^2 :=
      sum_le_sum fun b _ => square_multiples_card_bound b N
    _ = (N:ℝ) * ∑ b ∈ Ico K (N+1), 1/(b:ℝ)^2 := by simp [mul_sum, div_eq_mul_inv]
    _ ≤ (N:ℝ)*(2/K) := mul_le_mul_of_nonneg_left
      (Erdos371TerminalCompression.sum_reciprocal_sq hK _) (Nat.cast_nonneg N)
    _ = _ := by ring

lemma squareBad_count_bound {K : ℕ} (hK : 0 < K) (N : ℕ) :
    (((range N).filter (squareBad K)).card : ℝ) ≤ 1 + 2*N/K := by
  have hsub : (range N).filter (squareBad K) ⊆ insert 0 (squareCover K N) := by
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    obtain ⟨hnN, b, hbK, hbn⟩ := mem_filter.mp hn
    have hb : 0 < b := by omega
    have hbN : b ≤ N := by
      have hsq := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hbn
      have hnlt := mem_range.mp hnN
      nlinarith
    apply mem_insert_of_mem
    exact mem_biUnion.mpr ⟨b, mem_Ico.mpr ⟨by omega, by omega⟩,
      mem_filter.mpr ⟨hnN, hn0, hbn⟩⟩
  have hc := (card_le_card hsub).trans (card_insert_le _ _)
  have hcr : (((range N).filter (squareBad K)).card : ℝ) ≤ (squareCover K N).card + 1 := by
    exact_mod_cast hc
  linarith [squareCover_card_bound hK N]

lemma squareBad_density_bound {K : ℕ} (hK : 0 < K) {N : ℕ} (hN : 0 < N) :
    {n | squareBad K n}.partialDensity Set.univ N ≤ 1/N + 2/K := by
  rw [Erdos371Exploration.partialDensity_eq_count]
  calc
    _ ≤ (1 + 2*(N:ℝ)/K)/N := div_le_div_of_nonneg_right
      (squareBad_count_bound hK N) (Nat.cast_nonneg N)
    _ = _ := by field_simp


lemma partialDensity_mono {S T : Set ℕ} (h : S ⊆ T) (N : ℕ) :
    S.partialDensity Set.univ N ≤ T.partialDensity Set.univ N := by
  rw [← indicator_mean_eq_density, ← indicator_mean_eq_density]
  apply mean_mono
  intro n
  by_cases hn : n ∈ S
  · simp [hn, h hn]
  · simp only [if_neg hn]
    split_ifs <;> norm_num

noncomputable def lowThreshold (K : ℕ) : ℕ := ⌈excessBound K⌉₊ + 2

def largeSum (n : ℕ) : Prop := 3*(P n : ℝ) < completeSum n

lemma largeSum_subset (K : ℕ) :
    {n | largeSum n} ⊆
      ({n | 1 < tailRatio n} ∪ {n | P n ≤ lowThreshold K}) ∪ {n | squareBad K n} := by
  intro n hn
  by_contra h
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at h
  have ht : tailRatio n ≤ 1 := le_of_not_gt h.1.1
  have hp : lowThreshold K < P n := Nat.lt_of_not_ge h.1.2
  have hn1 : 1 < n := by
    have hpn : P n ≤ n := Nat.maxPrimeFac_le
    unfold lowThreshold at hp
    omega
  have hbound := completeSum_bound_of_no_large_square (by omega : 0 < n) h.2
  have hC : excessBound K ≤ (P n : ℝ) := by
    apply (Nat.le_ceil (excessBound K)).trans
    apply Nat.cast_le.mpr
    unfold lowThreshold at hp
    omega
  have hA := primeSum_upper hn1 ht
  change 3*(P n : ℝ) < completeSum n at hn
  linarith

lemma largeSum_density_bound {K : ℕ} (hK : 0 < K) {N : ℕ} (hN : 0 < N) :
    {n | largeSum n}.partialDensity Set.univ N ≤
      {n | 1 < tailRatio n}.partialDensity Set.univ N +
      {n | P n ≤ lowThreshold K}.partialDensity Set.univ N + 1/N + 2/K := by
  have h1 := partialDensity_mono (largeSum_subset K) N
  have h2 := Erdos371ComparableRatio.partialDensity_union_le
    ({n | 1 < tailRatio n} ∪ {n | P n ≤ lowThreshold K}) {n | squareBad K n} N
  have h3 := Erdos371ComparableRatio.partialDensity_union_le
    {n | 1 < tailRatio n} {n | P n ≤ lowThreshold K} N
  linarith [squareBad_density_bound hK hN]

/-- Repeated prime factors do not make the completely additive sum more than
three times its largest prime factor on a positive-density set. -/
theorem largeSum_hasDensity_zero : {n | largeSum n}.HasDensity 0 := by
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hKbig⟩ := exists_nat_gt (4/ε)
  have hK : 0 < K := Nat.cast_pos.mp ((by positivity : (0:ℝ) < 4/ε).trans hKbig)
  have hsmall : 2/(K:ℝ) < ε/2 := by
    have hk : (0:ℝ) < K := Nat.cast_pos.mpr hK
    have hh := (div_lt_iff₀ hε).mp hKbig
    apply (div_lt_iff₀ hk).mpr
    nlinarith
  have ht := tailRatio_exception_hasDensity_zero (by norm_num : (0:ℝ) < 1)
  have hp := Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero (lowThreshold K)
  have hu := (ht.add hp).add tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at hu
  filter_upwards [hu.eventually_lt_const (half_pos hε), eventually_gt_atTop 0]
    with N huN hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ {n | largeSum n}.partialDensity Set.univ N by
    unfold Set.partialDensity; positivity)]
  have hb := largeSum_density_bound hK hN
  change {n | 1 < tailRatio n}.partialDensity Set.univ N +
    {n | P n ≤ lowThreshold K}.partialDensity Set.univ N + 1/(N:ℝ) < ε/2 at huN
  linarith


def comparisonGood (n : ℕ) : Prop :=
  1 < n ∧ ¬largeSum n ∧ ¬largeSum (n+1) ∧
    3 * min (P n) (P (n+1)) < max (P n) (P (n+1))

lemma comparisonGood_complement_hasDensity_zero :
    {n | ¬comparisonGood n}.HasDensity 0 := by
  let A : Set ℕ := {n | P n ≤ 2}
  let B : Set ℕ := {n | largeSum n}
  let C : Set ℕ := {n | largeSum (n+1)}
  let D : Set ℕ := {n | max (P n) (P (n+1)) ≤ 3*min (P n) (P (n+1))}
  have hA : A.HasDensity 0 := Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero 2
  have hB : B.HasDensity 0 := largeSum_hasDensity_zero
  have hC : C.HasDensity 0 := Erdos371CofactorDensity.density_zero_shift (S := B) hB
  have hD : D.HasDensity 0 := Erdos371ComparableRatio.fixed_ratio_hasDensity_zero 3
  apply Erdos371Exploration.density_zero_of_subset (T := ((A ∪ B) ∪ C) ∪ D) _
    (Erdos371CofactorDensity.density_zero_union
      (Erdos371CofactorDensity.density_zero_union
        (Erdos371CofactorDensity.density_zero_union hA hB) hC) hD)
  intro n hn
  by_contra h
  simp only [Set.mem_union, not_or] at h
  have hp : ¬P n ≤ 2 := h.1.1.1
  have hb : ¬largeSum n := h.1.1.2
  have hc : ¬largeSum (n+1) := h.1.2
  have hd : ¬max (P n) (P (n+1)) ≤ 3*min (P n) (P (n+1)) := h.2
  have hpn : P n ≤ n := Nat.maxPrimeFac_le
  exact hn ⟨by omega, hb, hc, by omega⟩

lemma comparison_of_good {n : ℕ} (hg : comparisonGood n) :
    completeSum n < completeSum (n+1) ↔ P n < P (n+1) := by
  have hn := hg.1
  have hn1 : 1 < n+1 := by omega
  have hlo : (P n : ℝ) ≤ completeSum n :=
    (primeSum_lower hn).trans (primeSum_le_completeSum n)
  have hlo1 : (P (n+1) : ℝ) ≤ completeSum (n+1) :=
    (primeSum_lower hn1).trans (primeSum_le_completeSum (n+1))
  have hhi : completeSum n ≤ 3*(P n : ℝ) := le_of_not_gt hg.2.1
  have hhi1 : completeSum (n+1) ≤ 3*(P (n+1) : ℝ) := le_of_not_gt hg.2.2.1
  by_cases h : P n < P (n+1)
  · have hh : 3*P n < P (n+1) := by
      simpa [min_eq_left h.le, max_eq_right h.le] using hg.2.2.2
    have hhr : 3*(P n : ℝ) < (P (n+1) : ℝ) := by exact_mod_cast hh
    exact iff_of_true (hhi.trans_lt (hhr.trans_le hlo1)) h
  · have hne := consecutive_ne n
    have hr : P (n+1) < P n := by omega
    have hh : 3*P (n+1) < P n := by
      simpa [min_eq_right hr.le, max_eq_left hr.le] using hg.2.2.2
    have hhr : 3*(P (n+1) : ℝ) < (P n : ℝ) := by exact_mod_cast hh
    exact iff_of_false (not_lt_of_gt (hhi1.trans_lt (hhr.trans_le hlo))) h

/-- Counting prime factors with multiplicity does not change the direction of
the adjacent comparison outside a density-zero set. -/
theorem comparison_disagreement_hasDensity_zero :
    {n | ¬(completeSum n < completeSum (n+1) ↔ P n < P (n+1))}.HasDensity 0 := by
  apply Erdos371Exploration.density_zero_of_subset (T := {n | ¬comparisonGood n}) _
    comparisonGood_complement_hasDensity_zero
  intro n hn hg
  exact hn (comparison_of_good hg)

lemma comparison_indicator_difference_tendsto_zero :
    Tendsto (mean (fun n =>
      (if completeSum n < completeSum (n+1) then 1 else 0) -
      (if P n < P (n+1) then 1 else 0))) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    comparisonGood_complement_hasDensity_zero
  · exact fun _ => abs_nonneg _
  · intro N
    change |mean (fun n =>
      (if completeSum n < completeSum (n+1) then 1 else 0) -
      (if P n < P (n+1) then 1 else 0)) N| ≤
        {n | ¬comparisonGood n}.partialDensity Set.univ N
    rw [← indicator_mean_eq_density]
    unfold mean
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro n _
    by_cases hg : comparisonGood n
    · simp only [Set.mem_setOf_eq, hg, not_true_eq_false, if_false,
        comparison_of_good hg, sub_self, abs_zero, le_refl]
    · simp only [Set.mem_setOf_eq, hg, not_false_eq_true, if_true]
      split_ifs <;> norm_num

/-- This equivalence is not a proof of either half-density statement. -/
theorem density_half_iff_completeSum :
    {n | P n < P (n+1)}.HasDensity (1/2) ↔
      {n | completeSum n < completeSum (n+1)}.HasDensity (1/2) := by
  have he := comparison_indicator_difference_tendsto_zero
  have hA (N : ℕ) : mean (fun n => if P n < P (n+1) then 1 else 0) N =
      {n | P n < P (n+1)}.partialDensity Set.univ N :=
    by
      rw [← indicator_mean_eq_density]
      congr 1
      funext n
      by_cases h : P n < P (n+1) <;> simp [h]
  have hB (N : ℕ) : mean (fun n => if completeSum n < completeSum (n+1) then 1 else 0) N =
      {n | completeSum n < completeSum (n+1)}.partialDensity Set.univ N :=
    indicator_mean_eq_density {n | completeSum n < completeSum (n+1)} N
  change Tendsto (fun N => mean (fun n =>
    (if completeSum n < completeSum (n+1) then 1 else 0) -
    (if P n < P (n+1) then 1 else 0)) N) _ _ at he
  simp only [mean_sub, hA, hB] at he
  constructor
  · intro h
    have hh := h.add he
    simp only [add_zero] at hh
    apply hh.congr
    intro N
    ring
  · intro h
    have hh := h.sub he
    simp only [sub_zero] at hh
    apply hh.congr
    intro N
    ring

/-- The completely multiplicative Laplace transform of the additive sum. -/
noncomputable def laplace (t : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.exp (-t * completeSum n)

lemma laplace_mul (t : ℝ) (a b : ℕ) :
    laplace t (a*b) = laplace t a * laplace t b := by
  by_cases ha : a = 0
  · simp [ha, laplace]
  by_cases hb : b = 0
  · simp [hb, laplace]
  simp only [laplace, if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb),
    completeSum_mul ha hb, mul_add, Real.exp_add]

lemma laplace_bounds {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ laplace t n ∧ laplace t n ≤ 1 := by
  unfold laplace
  split_ifs
  · norm_num
  · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (completeSum_nonneg n))⟩

lemma laplace_comparison {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) :
    laplace t (n+1) < laplace t n ↔ completeSum n < completeSum (n+1) := by
  simp only [laplace, if_neg (Nat.ne_of_gt hn), if_neg (Nat.succ_ne_zero n),
    Real.exp_lt_exp]
  constructor <;> intro h <;> nlinarith

/-- Thus even one fixed, nonnegative completely multiplicative function has
adjacent descents encoding the original comparison outside a negligible set.
This does not assert the density of those descents. -/
theorem laplace_comparison_disagreement_hasDensity_zero {t : ℝ} (ht : 0 < t) :
    {n | ¬(laplace t (n+1) < laplace t n ↔ P n < P (n+1))}.HasDensity 0 := by
  apply Erdos371Exploration.density_zero_of_subset (T := {n | ¬comparisonGood n}) _
    comparisonGood_complement_hasDensity_zero
  intro n hn hg
  exact hn ((laplace_comparison ht (by have := hg.1; omega)).trans (comparison_of_good hg))

end Erdos371CompleteAdditiveComparison

#print axioms Erdos371CompleteAdditiveComparison.completeSum_mul
#print axioms Erdos371CompleteAdditiveComparison.largeSum_hasDensity_zero
#print axioms Erdos371CompleteAdditiveComparison.density_half_iff_completeSum
#print axioms Erdos371CompleteAdditiveComparison.laplace_mul

#print axioms Erdos371CompleteAdditiveComparison.laplace_comparison_disagreement_hasDensity_zero
