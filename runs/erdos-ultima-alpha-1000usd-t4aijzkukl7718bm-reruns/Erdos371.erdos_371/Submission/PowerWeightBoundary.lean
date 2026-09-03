import FormalConjecturesUtil
import Submission.AdditivePrimeDominance

/-! A nonuniformity obstruction for interpolating prime weights p^s to s=0.
This is not a disproof of Erdős 371 or of any fixed-positive-exponent estimate. -/

namespace Erdos371PowerWeightBoundary

open Finset Filter Erdos371PrimeDiscrepancy Erdos371SmallPrimeAveraging
open Erdos371AveragingCriterion Erdos371ReflectionRange
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def properPrimes (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun q => q<P n)

noncomputable def properCount (n : ℕ) : ℝ := (properPrimes n).card

noncomputable def powerTail (s : ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ properPrimes n, ((q:ℝ)/(P n:ℝ))^s

lemma powerTail_zero (n : ℕ) : powerTail 0 n=properCount n := by
  simp [powerTail,properCount]

lemma powerTail_one (n : ℕ) : powerTail 1 n=Erdos371AdditivePrimeDominance.tailRatio n := by
  simp [powerTail,properPrimes,Erdos371AdditivePrimeDominance.tailRatio,Finset.sum_filter]

lemma fixed_one_mean_tendsto_zero :
    Tendsto (mean (fun n => powerTail 1 (n+1))) atTop (𝓝 0) := by
  simpa only [powerTail_one] using
    Erdos371AdditivePrimeDominance.tailRatio_shift_mean_tendsto_zero

lemma primeFactors_card_bound (n : ℕ) :
    (n.primeFactors.card:ℝ) ≤ properCount n+1 := by
  have hsub : n.primeFactors ⊆ insert (P n) (properPrimes n) := by
    intro q hq
    by_cases h : q=P n
    · simp [h]
    · apply Finset.mem_insert_of_mem
      obtain ⟨hp,hd,hn⟩ := Nat.mem_primeFactors.mp hq
      have hle : q≤P n := Nat.le_maxPrimeFac hn hp hd
      exact Finset.mem_filter.mpr ⟨hq,by omega⟩
  have hh := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  simpa only [properCount,Nat.cast_add,Nat.cast_one] using (Nat.cast_le (α := ℝ).mpr hh)

lemma smallCount_le_primeFactors {s : Finset ℕ} (hs : ∀ p∈s,p.Prime) (n : ℕ) :
    smallCount s n≤((n+1).primeFactors.card:ℝ) := by
  rw [smallCount_eq_card]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hps,hd⟩ := Finset.mem_filter.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hs p hps,hd,by omega⟩

lemma smallCount_mean_tendsto {s : Finset ℕ} (hs : ∀ p∈s,p.Prime) :
    Tendsto (mean (smallCount s)) atTop (𝓝 (mass s)) := by
  have h := tendsto_finset_sum s (fun p hp => mean_ind_tendsto (hs p hp).pos)
  change Tendsto (fun N => mean (fun n => ∑ p∈s,ind p n) N) _ _
  simpa only [mean_sum,mass] using h

lemma mean_properCount_eventually_gt (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, B < mean (fun n => properCount (n+1)) N := by
  obtain ⟨s,hs,hM⟩ := prime_mass_unbounded (B+1)
  filter_upwards [(smallCount_mean_tendsto hs).eventually (lt_mem_nhds hM),
    eventually_gt_atTop 0] with N hN hpos
  have hh := mean_mono (fun n =>
    (smallCount_le_primeFactors hs n).trans (primeFactors_card_bound (n+1))) N
  rw [mean_add,mean_const 1 hpos] at hh
  linarith

/-- The boundary value at exponent zero has divergent, not vanishing, mean. -/
theorem properCount_shift_mean_tendsto_atTop :
    Tendsto (mean (fun n => properCount (n+1))) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro B
  exact (mean_properCount_eventually_gt B).mono (fun _ h => h.le)

lemma powerTail_continuous (n : ℕ) : Continuous (fun s : ℝ => powerTail s n) := by
  unfold powerTail
  apply continuous_finset_sum
  intro q hq
  obtain ⟨hq,hlt⟩ := Finset.mem_filter.mp hq
  have hprime := (Nat.mem_primeFactors.mp hq).1
  have hqpos : (0:ℝ)<q := Nat.cast_pos.mpr hprime.pos
  have hppos : (0:ℝ)<P n := Nat.cast_pos.mpr (hprime.pos.trans hlt)
  exact Real.continuous_const_rpow (div_pos hqpos hppos).ne'

lemma powerTail_mean_continuous (N : ℕ) :
    Continuous (fun s : ℝ => mean (fun n => powerTail s (n+1)) N) := by
  unfold mean
  exact (continuous_finset_sum (Finset.range N) (fun n _ => powerTail_continuous (n+1))).div_const _

/-- For arbitrarily large counting ranges, sufficiently small positive
exponents make the normalized tail mean arbitrarily large. Thus a bound
uniform over ALL positive exponents cannot transfer fixed-exponent domination
to the boundary s=0. No assertion about signed comparison means is made. -/
theorem arbitrarily_large_small_exponent_mean (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∃ s : ℝ, 0<s ∧
      B < mean (fun n => powerTail s (n+1)) N := by
  filter_upwards [mean_properCount_eventually_gt (B+1)] with N hN
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp
    (powerTail_mean_continuous N).continuousAt 1 (by norm_num)
  refine ⟨δ/2,half_pos hδ,?_⟩
  have hd : dist (δ/2) (0:ℝ)<δ := by
    rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hδ)]
    linarith
  have hh := hclose hd
  simp only [Real.dist_eq,powerTail_zero] at hh
  have hh' := (abs_lt.mp hh).1
  linarith

end Erdos371PowerWeightBoundary

#print axioms Erdos371PowerWeightBoundary.properCount_shift_mean_tendsto_atTop
#print axioms Erdos371PowerWeightBoundary.arbitrarily_large_small_exponent_mean
