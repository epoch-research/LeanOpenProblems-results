import FormalConjecturesUtil
import Submission.PositivePowerDominance
import Submission.NormalizedAdditiveDiscrepancy

/-! Uniform approximation of largest-prime comparison signs by normalized
prime-power sums, when the powers stay bounded away from zero. This proves
no cancellation of either signed mean and does not settle Erdős 371. -/

namespace Erdos371UniformPowerSkew

open Finset Filter Erdos371PrimeDiscrepancy Erdos371PositivePowerDominance
open Erdos371SmallPrimeAveraging Erdos371ReflectionRange
open Erdos371NormalizedAdditiveDiscrepancy (skew skew_swap skew_abs_le skew_error_bound)
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def powerSum (s : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (p:ℝ)^s

lemma powerSum_nonneg (s : ℝ) (n : ℕ) : 0 ≤ powerSum s n := by
  unfold powerSum
  positivity

lemma powerSum_eq (s : ℝ) {n : ℕ} (hn : 1<n) :
    powerSum s n = (P n:ℝ)^s * (1+tail s n) := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hp0 : (P n:ℝ)^s ≠ 0 :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) s).ne'
  have hmem : P n ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp,Nat.maxPrimeFac_dvd,by omega⟩
  have ht : (P n:ℝ)^s * tail s n =
      ∑ q ∈ n.primeFactors, if q<P n then (q:ℝ)^s else 0 := by
    unfold tail
    rw [mul_sum]
    apply sum_congr rfl
    intro q hq
    by_cases hqP : q<P n
    · simp only [if_pos hqP]
      rw [Real.div_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg (P n))]
      field_simp
    · simp [hqP]
  have he (q : ℕ) (hq : q ∈ n.primeFactors) : (q:ℝ)^s =
      (if q=P n then (P n:ℝ)^s else 0)+(if q<P n then (q:ℝ)^s else 0) := by
    obtain ⟨hqprime,hd,hn0⟩ := Nat.mem_primeFactors.mp hq
    have hle : q≤P n := Nat.le_maxPrimeFac hn0 hqprime hd
    by_cases h : q=P n
    · simp [h]
    · simp [h,show q<P n by omega]
  unfold powerSum
  rw [sum_congr rfl he,sum_add_distrib]
  simp only [sum_ite_eq',hmem,if_true]
  rw [← ht]
  ring

lemma powerSum_lower (s : ℝ) {n : ℕ} (hn : 1<n) : (P n:ℝ)^s ≤ powerSum s n := by
  rw [powerSum_eq s hn]
  nlinarith [tail_nonneg s n, show (0:ℝ)≤(P n:ℝ)^s by positivity]

lemma powerSum_upper (s : ℝ) {n : ℕ} (hn : 1<n) (ht : tail s n≤1) :
    powerSum s n ≤ 2*(P n:ℝ)^s := by
  rw [powerSum_eq s hn]
  nlinarith [show (0:ℝ)≤(P n:ℝ)^s by positivity]

lemma tail_exception_hasDensity_zero {δ ε : ℝ} (hδ : 0<δ) (hε : 0<ε) :
    {n | ε<tail δ n}.HasDensity 0 := by
  have hs := (tail_mean_tendsto_zero hδ).div_const ε
  simp only [zero_div] at hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
  · intro N
    unfold Set.partialDensity
    positivity
  · intro N
    change {n | ε<tail δ n}.partialDensity Set.univ N ≤ mean (tail δ) N/ε
    rw [← indicator_mean_eq_density]
    have he : mean (tail δ) N/ε = mean (fun n => tail δ n/ε) N := by
      simp [mean,sum_div,div_div,mul_comm]
    rw [he]
    apply mean_mono
    intro n
    by_cases h : ε<tail δ n
    · simp only [Set.mem_setOf_eq,h,if_true]
      exact (le_div_iff₀ hε).mpr (by linarith)
    · simp only [Set.mem_setOf_eq,h,if_false]
      exact div_nonneg (tail_nonneg δ n) hε.le

noncomputable def normalized (s : ℝ) (n : ℕ) : ℝ :=
  skew (powerSum s n) (powerSum s (n+1))

noncomputable def error (s : ℝ) (n : ℕ) : ℝ := |(sign n:ℝ)-normalized s n|

lemma normalized_abs_le (s : ℝ) (n : ℕ) : |normalized s n|≤1 :=
  skew_abs_le (powerSum_nonneg s n) (powerSum_nonneg s (n+1))

lemma error_nonneg (s : ℝ) (n : ℕ) : 0≤error s n := abs_nonneg _

lemma error_le_two (s : ℝ) (n : ℕ) : error s n≤2 := by
  have hs : |(sign n : ℝ)|=1 := by
    unfold sign
    split_ifs <;> norm_num
  have h := abs_sub (sign n : ℝ) (normalized s n)
  rw [hs] at h
  exact h.trans (by linarith [normalized_abs_le s n])

def good (δ : ℝ) (C n : ℕ) : Prop :=
  1<n ∧ tail δ n≤1 ∧ tail δ (n+1)≤1 ∧
    C*min (P n) (P (n+1))< max (P n) (P (n+1))

lemma not_good_hasDensity_zero {δ : ℝ} (hδ : 0<δ) (C : ℕ) :
    {n | ¬good δ C n}.HasDensity 0 := by
  let A : Set ℕ := {n | P n≤2}
  let B : Set ℕ := {n | 1<tail δ n}
  let D : Set ℕ := {n | max (P n) (P (n+1))≤C*min (P n) (P (n+1))}
  have hA : A.HasDensity 0 := Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero 2
  have hB : B.HasDensity 0 := tail_exception_hasDensity_zero hδ (by norm_num)
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
  have hb : ¬1<tail δ n := h.1.1.2
  have hb' : ¬1<tail δ (n+1) := h.1.2
  have hd : ¬max (P n) (P (n+1))≤C*min (P n) (P (n+1)) := h.2
  have hpn : P n≤n := Nat.maxPrimeFac_le
  exact hn ⟨by omega,le_of_not_gt hb,le_of_not_gt hb',by omega⟩

lemma scale_power_lower {δ s : ℝ} (hδ : 0<δ) (hs : δ≤s)
    {C p q : ℕ} (hC : 1≤C) (hrel : C*p≤q) :
    (C:ℝ)^δ * (p:ℝ)^s ≤ (q:ℝ)^s := by
  calc
    _ ≤ (C:ℝ)^s * (p:ℝ)^s := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hC) hs) (by positivity)
    _ = ((C:ℝ)*p)^s := (Real.mul_rpow (by positivity) (by positivity)).symm
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hrel)
      (hδ.trans_le hs).le

lemma error_of_good {δ s : ℝ} (hδ : 0<δ) (hs : δ≤s) {C n : ℕ}
    (hC : 1≤C) (hg : good δ C n) : error s n≤4/(C:ℝ)^δ := by
  have hnp : 1<n+1 := by have := hg.1; omega
  have hp : (0 : ℝ)<(P n:ℝ)^s := Real.rpow_pos_of_pos
    (Nat.cast_pos.mpr (Nat.prime_maxPrimeFac_of_one_lt n hg.1).pos) s
  have hq : (0 : ℝ)<(P (n+1):ℝ)^s := Real.rpow_pos_of_pos
    (Nat.cast_pos.mpr (Nat.prime_maxPrimeFac_of_one_lt (n+1) hnp).pos) s
  have hc : (0 : ℝ)<(C:ℝ)^δ := Real.rpow_pos_of_pos
    (Nat.cast_pos.mpr (by omega)) δ
  have ht₁ : tail s n≤1 := (tail_antitone n hs).trans hg.2.1
  have ht₂ : tail s (n+1)≤1 := (tail_antitone (n+1) hs).trans hg.2.2.1
  by_cases h : P n<P (n+1)
  · have hrel : (C:ℝ)^δ * (P n:ℝ)^s≤powerSum s (n+1) := by
      have hh : C*P n<P (n+1) := by
        simpa [min_eq_left h.le,max_eq_right h.le] using hg.2.2.2
      exact (scale_power_lower hδ hs hC hh.le).trans (powerSum_lower s hnp)
    simp only [error,sign,if_pos h,Int.cast_one,normalized]
    exact skew_error_bound (powerSum_nonneg s n) (hq.trans_le (powerSum_lower s hnp)) hc
      (powerSum_upper s hg.1 ht₁) hrel
  · have hne := consecutive_ne n
    have h' : P (n+1)<P n := by omega
    have hrel : (C:ℝ)^δ * (P (n+1):ℝ)^s≤powerSum s n := by
      have hh : C*P (n+1)<P n := by
        simpa [min_eq_right h'.le,max_eq_left h'.le] using hg.2.2.2
      exact (scale_power_lower hδ hs hC hh.le).trans (powerSum_lower s hg.1)
    have hh := skew_error_bound (powerSum_nonneg s (n+1))
      (hp.trans_le (powerSum_lower s hg.1)) hc (powerSum_upper s hnp ht₂) hrel
    rw [skew_swap] at hh
    have he : |(-1:ℝ)-normalized s n| =
        |1- -skew (powerSum s n) (powerSum s (n+1))| := by
      unfold normalized
      rw [show (-1:ℝ)-skew (powerSum s n) (powerSum s (n+1)) =
        -(1- -skew (powerSum s n) (powerSum s (n+1))) by ring,abs_neg]
    simpa only [error,sign,if_neg h,Int.cast_neg,Int.cast_one,he] using hh

lemma error_mean_bound {δ s : ℝ} (hδ : 0<δ) (hs : δ≤s) {C N : ℕ}
    (hC : 1≤C) (hN : 0<N) :
    mean (error s) N≤4/(C:ℝ)^δ+2*{n | ¬good δ C n}.partialDensity Set.univ N := by
  rw [← indicator_mean_eq_density,← mean_const (4/(C:ℝ)^δ) hN,
    ← mean_const_mul,← mean_add]
  apply mean_mono
  intro n
  by_cases h : good δ C n
  · simpa only [Set.mem_setOf_eq,h,not_true_eq_false,if_false,mul_zero,add_zero]
      using error_of_good hδ hs hC h
  · simp only [Set.mem_setOf_eq,h,not_false_eq_true,if_true,mul_one]
    exact (error_le_two s n).trans (by
      have h : (0:ℝ) ≤ 4/(C:ℝ)^δ := by positivity
      linarith)

/-- No upper bound on the moving exponents is required. The positive lower
bound is fixed before the counting limit. -/
theorem error_mean_tendsto_zero (exponent : ℕ → ℝ) {δ : ℝ}
    (hδ : 0<δ) (hs : ∀ᶠ N in atTop, δ≤exponent N) :
    Tendsto (fun N => mean (error (exponent N)) N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht := (tendsto_one_div_atTop_nhds_zero_nat.rpow_const (Or.inr hδ.le)).const_mul 4
  simp only [Real.zero_rpow hδ.ne',mul_zero] at ht
  have ht' : Tendsto (fun C : ℕ => 4/(C:ℝ)^δ) atTop (𝓝 0) := by
    apply ht.congr
    intro C
    rw [Real.div_rpow (by norm_num) (Nat.cast_nonneg C),Real.one_rpow]
    ring
  obtain ⟨C,hC,hsmall⟩ := ((eventually_ge_atTop 1).and
    (ht'.eventually_lt_const (half_pos hε))).exists
  have hd := (not_good_hasDensity_zero hδ C).eventually_lt_const
    (show (0:ℝ)<ε/4 by positivity)
  filter_upwards [hd,hs,eventually_gt_atTop 0] with N hdN hsN hN
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mean_nonneg (error_nonneg _) N)]
  have hh := error_mean_bound hδ hsN hC hN
  change 4/(C:ℝ)^δ<ε/2 at hsmall
  linarith

lemma mean_difference_tendsto_zero (exponent : ℕ → ℝ) {δ : ℝ}
    (hδ : 0<δ) (hs : ∀ᶠ N in atTop, δ≤exponent N) :
    Tendsto (fun N => mean (fun n => (sign n:ℝ)-normalized (exponent N) n) N)
      atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (error_mean_tendsto_zero exponent hδ hs)
  · intro N
    exact abs_nonneg _
  · intro N
    dsimp only [Function.comp_apply]
    unfold mean error
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)

/-- This is an equivalence, not a proof that the signed mean vanishes. -/
theorem density_half_iff_moving_normalized_mean_zero (exponent : ℕ → ℝ) {δ : ℝ}
    (hδ : 0<δ) (hs : ∀ᶠ N in atTop, δ≤exponent N) :
    {n | P n<P (n+1)}.HasDensity (1/2) ↔
      Tendsto (fun N => mean (normalized (exponent N)) N) atTop (𝓝 0) := by
  rw [density_half_iff_total_mean_zero]
  have he := mean_difference_tendsto_zero exponent hδ hs
  have hsign (N : ℕ) : mean (fun n => (sign n:ℝ)) N=(total N:ℝ)/N := by
    simp [mean,total]
  simp only [mean_sub,hsign] at he
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

/-- In absolute value the normalized skew has mean tending to one, uniformly
for exponents bounded away from zero. Its signed mean remains undetermined. -/
theorem absolute_mean_tendsto_one (exponent : ℕ → ℝ) {δ : ℝ}
    (hδ : 0<δ) (hs : ∀ᶠ N in atTop, δ≤exponent N) :
    Tendsto (fun N => mean (fun n => |normalized (exponent N) n|) N) atTop (𝓝 1) := by
  have hpoint (s : ℝ) (n : ℕ) : 1-|normalized s n| ≤ error s n := by
    have hsign : |(sign n:ℝ)|=1 := by unfold sign; split_ifs <;> norm_num
    have hh := abs_sub_abs_le_abs_sub (sign n:ℝ) (normalized s n)
    simpa only [hsign] using hh
  have hz : Tendsto (fun N => mean (fun n => 1-|normalized (exponent N) n|) N)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (error_mean_tendsto_zero exponent hδ hs)
    · intro N
      exact mean_nonneg (fun n => sub_nonneg.mpr (normalized_abs_le _ n)) N
    · intro N
      exact mean_mono (hpoint _) N
  have ht := (tendsto_const_nhds (x := (1:ℝ))).sub hz
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [mean_sub,mean_const 1 hN]
  ring

end Erdos371UniformPowerSkew

#print axioms Erdos371UniformPowerSkew.error_mean_tendsto_zero

#print axioms Erdos371UniformPowerSkew.density_half_iff_moving_normalized_mean_zero
#print axioms Erdos371UniformPowerSkew.absolute_mean_tendsto_one
