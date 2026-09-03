import FormalConjecturesUtil
import Submission.AdditivePrimeDominance

/-! A bounded normalized additive increment approximates the comparison sign
in mean absolute value. Its signed mean has NOT been proved to vanish. -/

namespace Erdos371NormalizedAdditiveDiscrepancy

open Finset Filter Erdos371PrimeDiscrepancy Erdos371AdditivePrimeDominance
open Erdos371SmallPrimeAveraging Erdos371ReflectionRange
open scoped Topology

noncomputable def skew (a b : ℝ) : ℝ := (b-a)/(a+b)

lemma skew_swap (a b : ℝ) : skew b a = -skew a b := by
  unfold skew
  rw [add_comm b a]
  ring

lemma skew_abs_le {a b : ℝ} (ha : 0≤a) (hb : 0≤b) : |skew a b|≤1 := by
  by_cases h : a+b=0
  · simp [skew,h]
  · have hpos : 0<a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h)
    rw [skew,abs_div,abs_of_pos hpos]
    apply (div_le_iff₀ hpos).mpr
    rw [one_mul,abs_le]
    constructor <;> linarith

lemma skew_error_bound {a b p C : ℝ} (ha : 0≤a) (hb : 0<b) (hC : 0<C)
    (hap : a≤2*p) (hpb : C*p≤b) : |1-skew a b|≤4/C := by
  have hab : 0<a+b := by linarith
  have he : 1-skew a b=2*a/(a+b) := by
    unfold skew
    field_simp
    ring
  rw [he,abs_of_nonneg (div_nonneg (by positivity) hab.le)]
  apply (div_le_div_iff₀ hab hC).mpr
  have hmul := mul_le_mul_of_nonneg_right hap hC.le
  nlinarith

noncomputable def normalized (n : ℕ) : ℝ := skew (primeSum n) (primeSum (n+1))
noncomputable def error (n : ℕ) : ℝ := |(sign n : ℝ)-normalized n|

lemma primeSum_nonneg (n : ℕ) : 0≤primeSum n := by
  unfold primeSum
  positivity

lemma normalized_abs_le (n : ℕ) : |normalized n|≤1 :=
  skew_abs_le (primeSum_nonneg n) (primeSum_nonneg (n+1))

lemma error_nonneg (n : ℕ) : 0≤error n := abs_nonneg _

lemma error_le_two (n : ℕ) : error n≤2 := by
  have hs : |(sign n : ℝ)|=1 := by
    unfold sign
    split_ifs <;> norm_num
  have h := abs_sub (sign n : ℝ) (normalized n)
  rw [hs] at h
  exact h.trans (by linarith [normalized_abs_le n])

def good (C n : ℕ) : Prop :=
  1<n ∧ tailRatio n≤1 ∧ tailRatio (n+1)≤1 ∧
    C*min (P n) (P (n+1))< max (P n) (P (n+1))

lemma not_good_hasDensity_zero (C : ℕ) : {n | ¬good C n}.HasDensity 0 := by
  let A : Set ℕ := {n | P n≤2}
  let B : Set ℕ := {n | 1<tailRatio n}
  let D : Set ℕ := {n | max (P n) (P (n+1))≤C*min (P n) (P (n+1))}
  have hA : A.HasDensity 0 := Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero 2
  have hB : B.HasDensity 0 := tailRatio_exception_hasDensity_zero (by norm_num)
  have hB' : {n | n+1∈B}.HasDensity 0 :=
    Erdos371CofactorDensity.density_zero_shift (S := B) hB
  have hD : D.HasDensity 0 := Erdos371ComparableRatio.fixed_ratio_hasDensity_zero C
  have hU := Erdos371CofactorDensity.density_zero_union
    (Erdos371CofactorDensity.density_zero_union
      (Erdos371CofactorDensity.density_zero_union hA hB) hB') hD
  apply Erdos371Exploration.density_zero_of_subset
    (T := ((A∪B)∪{n | n+1∈B})∪D) _ hU
  intro n hn
  by_contra h
  simp only [Set.mem_union,not_or] at h
  have ha : ¬P n≤2 := h.1.1.1
  have hb : ¬1<tailRatio n := h.1.1.2
  have hb' : ¬1<tailRatio (n+1) := h.1.2
  have hd : ¬max (P n) (P (n+1))≤C*min (P n) (P (n+1)) := h.2
  have hpn : P n≤n := Nat.maxPrimeFac_le
  exact hn ⟨by omega,le_of_not_gt hb,le_of_not_gt hb',by omega⟩

lemma error_of_good {C n : ℕ} (hC : 0<C) (hg : good C n) : error n≤4/(C : ℝ) := by
  have hnp : 1<n+1 := by have := hg.1; omega
  have hp : (0 : ℝ)<P n := Nat.cast_pos.mpr
    (Nat.prime_maxPrimeFac_of_one_lt n hg.1).pos
  have hq : (0 : ℝ)<P (n+1) := Nat.cast_pos.mpr
    (Nat.prime_maxPrimeFac_of_one_lt (n+1) hnp).pos
  have hc : (0 : ℝ)<C := Nat.cast_pos.mpr hC
  by_cases h : P n<P (n+1)
  · have hrel : (C : ℝ)*(P n : ℝ)≤primeSum (n+1) := by
      have hh : C*P n<P (n+1) := by
        simpa [min_eq_left h.le,max_eq_right h.le] using hg.2.2.2
      exact (show (C : ℝ)*(P n : ℝ)≤(P (n+1) : ℝ) by exact_mod_cast hh.le).trans
        (primeSum_lower hnp)
    simp only [error,sign,if_pos h,Int.cast_one,normalized]
    exact skew_error_bound (primeSum_nonneg n) (hq.trans_le (primeSum_lower hnp)) hc
      (primeSum_upper hg.1 hg.2.1) hrel
  · have hne := consecutive_ne n
    have h' : P (n+1)<P n := by omega
    have hrel : (C : ℝ)*(P (n+1) : ℝ)≤primeSum n := by
      have hh : C*P (n+1)<P n := by
        simpa [min_eq_right h'.le,max_eq_left h'.le] using hg.2.2.2
      exact (show (C : ℝ)*(P (n+1) : ℝ)≤(P n : ℝ) by exact_mod_cast hh.le).trans
        (primeSum_lower hg.1)
    have hh := skew_error_bound (primeSum_nonneg (n+1))
      (hp.trans_le (primeSum_lower hg.1)) hc (primeSum_upper hnp hg.2.2.1) hrel
    rw [skew_swap] at hh
    have he : |(-1 : ℝ)-normalized n|=|1- -skew (primeSum n) (primeSum (n+1))| := by
      unfold normalized
      rw [show (-1 : ℝ)-skew (primeSum n) (primeSum (n+1)) =
        -(1- -skew (primeSum n) (primeSum (n+1))) by ring,abs_neg]
    simpa only [error,sign,if_neg h,Int.cast_neg,Int.cast_one,he] using hh

lemma error_mean_bound {C N : ℕ} (hC : 0<C) (hN : 0<N) :
    mean error N≤4/(C : ℝ)+2*{n | ¬good C n}.partialDensity Set.univ N := by
  classical
  rw [← indicator_mean_eq_density,← mean_const (4/(C : ℝ)) hN,← mean_const_mul,← mean_add]
  apply mean_mono
  intro n
  by_cases h : good C n
  · simpa only [Set.mem_setOf_eq,h,not_true_eq_false,if_false,mul_zero,add_zero]
      using error_of_good hC h
  · simp only [Set.mem_setOf_eq,h,not_false_eq_true,if_true,mul_one]
    exact (error_le_two n).trans (by
      have h : (0 : ℝ) ≤ 4/(C : ℝ) := by positivity
      linarith)

/-- The normalized additive increment converges to the comparison sign in
mean absolute error. This does not assert that either signed mean vanishes. -/
theorem error_mean_tendsto_zero : Tendsto (mean error) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C,hCbig⟩ := exists_nat_gt (8/ε)
  have hC : 0<C := by
    have hp : (0 : ℝ)<8/ε := by positivity
    exact Nat.cast_pos.mp (hp.trans hCbig)
  have hCr : (0 : ℝ)<C := Nat.cast_pos.mpr hC
  have hsmall : 4/(C : ℝ)<ε/2 := by
    have hh := (div_lt_iff₀ hε).mp hCbig
    apply (div_lt_iff₀ hCr).mpr
    nlinarith
  have hd := (not_good_hasDensity_zero C).eventually_lt_const
    (show (0 : ℝ)<ε/4 by positivity)
  filter_upwards [hd,eventually_gt_atTop 0] with N hdN hN
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mean_nonneg error_nonneg N)]
  have hh := error_mean_bound hC hN
  linarith

lemma mean_difference_tendsto_zero :
    Tendsto (mean (fun n => (sign n : ℝ)-normalized n)) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds error_mean_tendsto_zero
  · intro N
    exact abs_nonneg _
  · intro N
    change |mean (fun n => (sign n : ℝ)-normalized n) N|≤ mean error N
    unfold mean error
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
      (Nat.cast_nonneg (α := ℝ) N)

/-- An exact reformulation, with the required limit still unproved. -/
theorem density_half_iff_normalized_mean_zero :
    {n | P n<P (n+1)}.HasDensity (1/2) ↔
      Tendsto (mean normalized) atTop (𝓝 0) := by
  rw [density_half_iff_total_mean_zero]
  have he := mean_difference_tendsto_zero
  have hs (N : ℕ) : mean (fun n => (sign n : ℝ)) N=(total N : ℝ)/N := by
    simp [mean,total]
  change Tendsto (fun N => mean (fun n => (sign n : ℝ)-normalized n) N) _ _ at he
  simp only [mean_sub,hs] at he
  constructor
  · intro h
    have hh := h.sub he
    simp only [sub_zero] at hh
    apply hh.congr
    intro N
    ring
  · intro h
    have hh := h.add he
    simp only [add_zero] at hh
    apply hh.congr
    intro N
    ring

/-- Normalizing each increment destroys ordinary telescoping, even around
a positive three-cycle. This is not an arithmetic counterexample. -/
lemma skew_three_cycle : skew 1 2+skew 2 3+skew 3 1=(1/30 : ℝ) := by
  norm_num [skew]

end Erdos371NormalizedAdditiveDiscrepancy

#print axioms Erdos371NormalizedAdditiveDiscrepancy.error_mean_tendsto_zero
#print axioms Erdos371NormalizedAdditiveDiscrepancy.density_half_iff_normalized_mean_zero
