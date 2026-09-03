import FormalConjecturesUtil
import Submission.CompleteAdditiveComparison

/-! A cutoff-dependent, completely additive reversal of the prime-factor sum.
Its prime values are positive and increasing throughout the counting range.
No universal descent bound for such functions is asserted here. -/

set_option maxHeartbeats 1000000

namespace Erdos371MonotoneAdditiveReversal

open Finset Filter Erdos371PrimeDiscrepancy Erdos371CompleteAdditiveComparison
open Erdos371AdditivePrimeDominance Erdos371SmallPrimeAveraging
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def height (N n : ℕ) : ℝ :=
  (N : ℝ)*Real.log (n : ℝ)-completeSum n

lemma height_mul (N : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    height N (a*b) = height N a + height N b := by
  unfold height
  rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb),
    completeSum_mul ha hb]
  ring

@[simp] lemma height_one (N : ℕ) : height N 1 = 0 := by simp [height]

lemma height_prime (N : ℕ) {p : ℕ} (hp : p.Prime) :
    height N p = (N : ℝ)*Real.log (p : ℝ)-p := by
  simp [height, completeSum, Nat.primeFactorsList_prime hp]

lemma log_difference_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b-a)/b ≤ Real.log b-Real.log a := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  have he : (b-a)/b = 1-a/b := by field_simp
  rw [he]
  linarith

lemma height_prime_monotone {N p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≤ q) (hqN : q ≤ N) : height N p ≤ height N q := by
  rw [height_prime N hp, height_prime N hq]
  have hpr : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq.pos
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpqr : (p : ℝ) ≤ q := Nat.cast_le.mpr hpq
  have hqNr : (q : ℝ) ≤ N := Nat.cast_le.mpr hqN
  have hlog : 0 ≤ Real.log (q : ℝ)-Real.log p := sub_nonneg.mpr
    (Real.log_le_log hpr hpqr)
  have hlo := log_difference_lower hpr hqr
  have hlo' := (div_le_iff₀ hqr).mp hlo
  have hh := mul_le_mul_of_nonneg_right hqNr hlog
  nlinarith

lemma height_prime_pos {N p : ℕ} (hN : 5 ≤ N) (hp : p.Prime) (hpN : p ≤ N) :
    0 < height N p := by
  have htwo : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hN' : (5 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have ht : 0 < height N 2 := by
    rw [height_prime N Nat.prime_two]
    have hh := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (α := ℝ) N)
    norm_num
    nlinarith
  exact ht.trans_le (height_prime_monotone Nat.prime_two hp hp.two_le hpN)

lemma log_increment_bounds {n : ℕ} (hn : 0 < n) :
    0 < Real.log ((n+1 : ℕ) : ℝ)-Real.log (n : ℝ) ∧
    Real.log ((n+1 : ℕ) : ℝ)-Real.log (n : ℝ) ≤ 1/(n : ℝ) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hns : (0 : ℝ) < (n+1 : ℕ) := by positivity
  constructor
  · exact sub_pos.mpr (Real.log_lt_log hnr (by exact_mod_cast Nat.lt_succ_self n))
  · have h := Real.log_le_sub_one_of_pos (div_pos hns hnr)
    rw [Real.log_div hns.ne' hnr.ne'] at h
    have he : ((n+1 : ℕ) : ℝ)/(n : ℝ)-1 = 1/(n : ℝ) := by
      push_cast
      field_simp
      ring
    simpa only [he] using h

lemma reverse_comparison {N n K : ℕ} (hn : 0 < n) (hNK : N ≤ K*n)
    (hgap : (K : ℝ) < |completeSum (n+1)-completeSum n|) :
    height N (n+1) < height N n ↔ completeSum n < completeSum (n+1) := by
  have hb := log_increment_bounds hn
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hNK' : (N : ℝ) ≤ (K : ℝ)*n := by exact_mod_cast hNK
  have hmul : (N : ℝ)*(Real.log ((n+1 : ℕ) : ℝ)-Real.log n) ≤ K := by
    calc
      _ ≤ (N : ℝ)*(1/(n : ℝ)) := mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg N)
      _ ≤ _ := by apply (div_le_iff₀ hnr).mpr at hNK'; simpa [div_eq_mul_inv] using hNK'
  have hnonneg : 0 ≤ (N : ℝ)*(Real.log ((n+1 : ℕ) : ℝ)-Real.log n) :=
    mul_nonneg (Nat.cast_nonneg N) hb.1.le
  unfold height
  constructor
  · intro h
    nlinarith
  · intro h
    rw [abs_of_pos (sub_pos.mpr h)] at hgap
    nlinarith

/-- Fixed bounded adjacent gaps in the completely additive prime sum are rare. -/
theorem bounded_gap_hasDensity_zero (K : ℕ) :
    {n | |completeSum (n+1)-completeSum n| ≤ (K : ℝ)}.HasDensity 0 := by
  let A : Set ℕ := {n | P n ≤ 2*K+2}
  let B : Set ℕ := {n | largeSum n}
  let C : Set ℕ := {n | largeSum (n+1)}
  let D : Set ℕ := {n | max (P n) (P (n+1)) ≤ 6*min (P n) (P (n+1))}
  have ha : A.HasDensity 0 := Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero _
  have hb : B.HasDensity 0 := largeSum_hasDensity_zero
  have hc : C.HasDensity 0 := Erdos371CofactorDensity.density_zero_shift (S := B) hb
  have hd : D.HasDensity 0 := Erdos371ComparableRatio.fixed_ratio_hasDensity_zero 6
  apply Erdos371Exploration.density_zero_of_subset (T := ((A∪B)∪C)∪D) _
    (Erdos371CofactorDensity.density_zero_union
      (Erdos371CofactorDensity.density_zero_union
        (Erdos371CofactorDensity.density_zero_union ha hb) hc) hd)
  intro n hgap
  by_contra hh
  simp only [Set.mem_union, not_or] at hh
  have hpn : 2*K+2 < P n := Nat.lt_of_not_ge hh.1.1.1
  have hn : 1 < n := by
    have h : P n ≤ n := Nat.maxPrimeFac_le
    omega
  have hlo : (P n : ℝ) ≤ completeSum n :=
    (primeSum_lower hn).trans (primeSum_le_completeSum n)
  have hlo' : (P (n+1) : ℝ) ≤ completeSum (n+1) :=
    (primeSum_lower (by omega : 1 < n+1)).trans (primeSum_le_completeSum (n+1))
  have hhi : completeSum n ≤ 3*(P n : ℝ) := le_of_not_gt hh.1.1.2
  have hhi' : completeSum (n+1) ≤ 3*(P (n+1) : ℝ) := le_of_not_gt hh.1.2
  have hr : 6*min (P n) (P (n+1)) < max (P n) (P (n+1)) := Nat.lt_of_not_ge hh.2
  have hpn' : 2*(K : ℝ)+2 < P n := by exact_mod_cast hpn
  change |completeSum (n+1)-completeSum n| ≤ (K : ℝ) at hgap
  change |completeSum (n+1)-completeSum n| ≤ (K : ℝ) at hgap
  have hab := abs_le.mp hgap
  by_cases horder : P n ≤ P (n+1)
  · rw [min_eq_left horder, max_eq_right horder] at hr
    have hr' : 6*(P n : ℝ) < P (n+1) := by exact_mod_cast hr
    nlinarith
  · have horder' : P (n+1) ≤ P n := Nat.le_of_not_ge horder
    rw [min_eq_right horder', max_eq_left horder'] at hr
    have hr' : 6*(P (n+1) : ℝ) < P n := by exact_mod_cast hr
    nlinarith


def disagreement (N n : ℕ) : Prop :=
  ¬(height N (n+1) < height N n ↔ completeSum n < completeSum (n+1))

lemma disagreement_count_bound {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ((range N).filter (disagreement N)).card ≤
      ((range N).filter (fun n => |completeSum (n+1)-completeSum n| ≤ (K : ℝ))).card +
      (N/K+1) := by
  have hs : (range N).filter (disagreement N) ⊆
      ((range N).filter (fun n => |completeSum (n+1)-completeSum n| ≤ (K : ℝ))) ∪
      range (N/K+1) := by
    intro n hn
    obtain ⟨hnN, hdis⟩ := mem_filter.mp hn
    by_cases hgap : |completeSum (n+1)-completeSum n| ≤ (K : ℝ)
    · exact mem_union_left _ (mem_filter.mpr ⟨hnN,hgap⟩)
    · apply mem_union_right
      apply mem_range.mpr
      by_contra hlarge
      have hdiv : N/K < n := by omega
      have hNK : N ≤ K*n := by
        have hh : ¬ n ≤ N/K := by omega
        rw [Nat.le_div_iff_mul_le hK] at hh
        nlinarith
      have hn0 : 0 < n := (Nat.zero_le (N/K)).trans_lt hdiv
      exact hdis (reverse_comparison hn0 hNK (lt_of_not_ge hgap))
  exact (card_le_card hs).trans (by simpa only [card_range] using (card_union_le
    ((range N).filter (fun n => |completeSum (n+1)-completeSum n| ≤ (K : ℝ)))
    (range (N/K+1))))

lemma disagreement_density_bound {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    {n | disagreement N n}.partialDensity Set.univ N ≤
      {n | |completeSum (n+1)-completeSum n| ≤ (K : ℝ)}.partialDensity Set.univ N +
      1/(K : ℝ)+1/(N : ℝ) := by
  rw [Erdos371Exploration.partialDensity_eq_count,
    Erdos371Exploration.partialDensity_eq_count]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  calc
    _ ≤ (((range N).filter (fun n => |completeSum (n+1)-completeSum n| ≤ (K : ℝ))).card +
        ((N/K : ℕ) : ℝ)+1)/(N : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      exact_mod_cast disagreement_count_bound hK N
    _ ≤ (((range N).filter (fun n => |completeSum (n+1)-completeSum n| ≤ (K : ℝ))).card +
        (N : ℝ)/K+1)/(N : ℝ) := by
      exact div_le_div_of_nonneg_right (by linarith [Nat.cast_div_le (m := N) (n := K) (α := ℝ)])
        (Nat.cast_nonneg N)
    _ = _ := by field_simp

/-- Reversal disagreements have vanishing density even though the height
function itself changes at each counting cutoff. -/
theorem disagreement_density_tendsto_zero :
    Tendsto (fun N : ℕ => {n | disagreement N n}.partialDensity Set.univ N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hKbig⟩ := exists_nat_gt (4/ε)
  have hK : 0 < K := Nat.cast_pos.mp ((by positivity : (0 : ℝ) < 4/ε).trans hKbig)
  have hk : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hsmall : 1/(K : ℝ) < ε/2 := by
    have hh := (div_lt_iff₀ hε).mp hKbig
    apply (div_lt_iff₀ hk).mpr
    nlinarith
  have hh := (bounded_gap_hasDensity_zero K).add tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at hh
  filter_upwards [hh.eventually_lt_const (half_pos hε), eventually_gt_atTop 0] with N hbound hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤
    {n | disagreement N n}.partialDensity Set.univ N by unfold Set.partialDensity; positivity)]
  have hb := disagreement_density_bound hK hN
  change {n | |completeSum (n+1)-completeSum n| ≤ (K : ℝ)}.partialDensity Set.univ N +
    1/(N : ℝ) < ε/2 at hbound
  linarith

noncomputable def descentMean (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  mean (fun n => if f (n+1) < f n then 1 else 0) N

noncomputable def ascentMean (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  mean (fun n => if f n < f (n+1) then 1 else 0) N

lemma reversal_mean_error_bound (N : ℕ) :
    |descentMean (height N) N-ascentMean completeSum N| ≤
      {n | disagreement N n}.partialDensity Set.univ N := by
  rw [descentMean, ascentMean, ← mean_sub, ← Erdos371ReflectionRange.indicator_mean_eq_density]
  unfold mean
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  by_cases h : disagreement N n
  · simp only [Set.mem_setOf_eq, h, if_true]
    split_ifs <;> norm_num
  · have he : height N (n+1) < height N n ↔ completeSum n < completeSum (n+1) :=
      Classical.not_not.mp h
    simp only [Set.mem_setOf_eq, h, if_false, he, sub_self, abs_zero, le_refl]

theorem reversal_mean_difference_tendsto_zero :
    Tendsto (fun N : ℕ => descentMean (height N) N-ascentMean completeSum N) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds disagreement_density_tendsto_zero
  · intro N; exact abs_nonneg _
  · intro N; exact reversal_mean_error_bound N

/-- The finite-range class needed by the proposed descent bound. -/
def admissible (N : ℕ) (f : ℕ → ℝ) : Prop :=
  f 1 = 0 ∧
  (∀ a b, a ≠ 0 → b ≠ 0 → f (a*b) = f a+f b) ∧
  (∀ p, p.Prime → p ≤ N → 0 < f p) ∧
  (∀ p q, p.Prime → q.Prime → p ≤ q → q ≤ N → f p ≤ f q)

lemma completeSum_admissible (N : ℕ) : admissible N completeSum := by
  refine ⟨completeSum_one, fun a b ha hb => completeSum_mul ha hb, ?_, ?_⟩
  · intro p hp hpN
    simp only [completeSum, Nat.primeFactorsList_prime hp, List.map_singleton, List.sum_singleton]
    exact Nat.cast_pos.mpr hp.pos
  · intro p q hp hq hpq hqN
    simpa only [completeSum, Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq,
      List.map_singleton, List.sum_singleton] using (Nat.cast_le.mpr hpq : (p : ℝ) ≤ q)

lemma height_admissible {N : ℕ} (hN : 5 ≤ N) : admissible N (height N) :=
  ⟨height_one N, fun _ _ ha hb => height_mul N ha hb,
    fun _ hp hpN => height_prime_pos hN hp hpN,
    fun _ _ hp hq hpq hqN => height_prime_monotone hp hq hpq hqN⟩

noncomputable def tieMean (N : ℕ) : ℝ :=
  mean (fun n => if completeSum n = completeSum (n+1) then 1 else 0) N

lemma tieMean_tendsto_zero : Tendsto tieMean atTop (𝓝 0) := by
  have he (N : ℕ) : tieMean N =
      {n | |completeSum (n+1)-completeSum n| ≤ (0 : ℝ)}.partialDensity Set.univ N := by
    rw [← Erdos371ReflectionRange.indicator_mean_eq_density]
    simp only [tieMean, Set.mem_setOf_eq, abs_nonpos_iff, sub_eq_zero, eq_comm]
  change Tendsto (fun N : ℕ => tieMean N) atTop (𝓝 0)
  simp_rw [he]
  simpa only [Nat.cast_zero] using bounded_gap_hasDensity_zero 0

lemma ascent_descent_tie {N : ℕ} (hN : 0 < N) :
    ascentMean completeSum N+descentMean completeSum N+tieMean N = 1 := by
  unfold ascentMean descentMean tieMean
  rw [← mean_add, ← mean_add]
  have he (n : ℕ) :
      (if completeSum n < completeSum (n+1) then (1 : ℝ) else 0) +
      (if completeSum (n+1) < completeSum n then 1 else 0) +
      (if completeSum n = completeSum (n+1) then 1 else 0) = 1 := by
    rcases lt_trichotomy (completeSum n) (completeSum (n+1)) with h | h | h
    · simp [h, not_lt_of_ge h.le, h.ne]
    · simp [h]
    · simp [h, not_lt_of_ge h.le, h.ne']
  simp_rw [he]
  exact mean_const 1 hN

/-- A genuinely sufficient uniform one-sided descent criterion. The uniform
bound in the hypothesis is NOT established by this file. -/
theorem density_half_of_uniform_monotone_descent_bound
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ f : ℕ → ℝ, admissible N f → descentMean f N ≤ 1/2+ε) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  apply density_half_iff_completeSum.mpr
  have hm : Tendsto (ascentMean completeSum) atTop (𝓝 (1/2)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have herr := (reversal_mean_difference_tendsto_zero.abs).eventually_lt_const
      (show |(0 : ℝ)| < ε/4 by simpa using (show (0 : ℝ) < ε/4 by positivity))
    have htie := tieMean_tendsto_zero.eventually_lt_const (show (0 : ℝ) < ε/4 by positivity)
    filter_upwards [h (ε/4) (by positivity), herr, htie, eventually_ge_atTop 5]
      with N hbound herrN htieN hN
    have hpos : 0 < N := by omega
    have hS := hbound completeSum (completeSum_admissible N)
    have hR := hbound (height N) (height_admissible hN)
    have hsplit := ascent_descent_tie hpos
    have he := abs_lt.mp herrN
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith
  apply hm.congr
  intro N
  exact Erdos371ReflectionRange.indicator_mean_eq_density _ N

end Erdos371MonotoneAdditiveReversal

#print axioms Erdos371MonotoneAdditiveReversal.bounded_gap_hasDensity_zero

#print axioms Erdos371MonotoneAdditiveReversal.disagreement_density_tendsto_zero
#print axioms Erdos371MonotoneAdditiveReversal.density_half_of_uniform_monotone_descent_bound
