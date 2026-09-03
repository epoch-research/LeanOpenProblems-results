import FormalConjecturesUtil
import Submission.PrimeBinBilinear
import Submission.SubpowerCutoff

/-! Quantitative sufficient bounds for the fixed-cutoff signed prime blocks.
  The required signed block estimate is an explicit hypothesis throughout. -/

namespace Erdos371PrimeBinCriterion

open Finset Filter Erdos371PrimeBinKernel Erdos371PrimeBinBilinear
open Erdos371PrimeDiscrepancy Erdos371SmallPrimeAveraging
open Erdos371CroppedEnergy Erdos371SubpowerCutoff
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def lowBins (K N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun k => 2^k≤N/K
noncomputable def highBins (K N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun k => ¬2^k≤N/K

lemma sum_low_scales (K N : ℕ) :
    (∑ k ∈ lowBins K N,(2:ℝ)^k) ≤ 2*(N/K:ℕ) := by
  by_cases hz : N/K=0
  · have he : lowBins K N=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      have hh := (Finset.mem_filter.mp hk).2
      have hp := Nat.one_le_two_pow (n := k)
      omega
    simp [he,hz]
  · have hsub : lowBins K N ⊆ Finset.range (Nat.log 2 (N/K)+1) := by
      intro k hk
      have hh := Nat.le_log_of_pow_le (by decide : 1<(2:ℕ)) (Finset.mem_filter.mp hk).2
      exact Finset.mem_range.mpr (by omega)
    have hp : (2:ℝ)^(Nat.log 2 (N/K)) ≤ (N/K:ℕ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hz
    calc
      _ ≤ ∑ k ∈ Finset.range (Nat.log 2 (N/K)+1),(2:ℝ)^k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = (2:ℝ)^(Nat.log 2 (N/K)+1)-1 := by
        have hg := geom_sum_mul (2:ℝ) (Nat.log 2 (N/K)+1)
        norm_num at hg
        exact hg
      _ ≤ 2*(N/K:ℕ) := by rw [pow_succ]; linarith

lemma high_bin_kernel_abs (K N n : ℕ) (hK : 0<K) (hn : n<N) :
    |(∑ k ∈ highBins K N,(kernel k n:ℝ))| ≤
      if n/P n≤K ∨ (n+1)/P (n+1)≤K then 1 else 0 := by
  simp only [kernel_eq_single,Int.cast_ite,Int.cast_zero,Finset.sum_ite_eq']
  by_cases hi : index n∈highBins K N
  · simp only [if_pos hi]
    by_cases hz : binnedSign n=0
    · simp only [hz,Int.cast_zero,abs_zero]
      split_ifs <;> norm_num
    · have hs := kernel_support hz
      have hw := (Erdos371PrimeHarmonicBlocks.mem_block.mp hs).2.1
      have hh := (Finset.mem_filter.mp hi).2
      have hb := high_winner_bad hK hn (by omega : N/K<winner n)
      rw [if_pos hb]
      exact_mod_cast kernel_abs_le_one (index n) n
  · simp only [if_neg hi,abs_zero]
    split_ifs <;> norm_num

lemma high_bin_total_abs_le (K N : ℕ) (hK : 0<K) :
    |(∑ k ∈ highBins K N,∑ n ∈ Finset.range N,(kernel k n:ℝ))| ≤ badCount K N := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ n ∈ Finset.range N, |∑ k ∈ highBins K N,(kernel k n:ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N,
        if n/P n≤K ∨ (n+1)/P (n+1)≤K then (1:ℝ) else 0 :=
      Finset.sum_le_sum (fun n hn => high_bin_kernel_abs K N n hK (Finset.mem_range.mp hn))
    _ = _ := by simp only [Finset.sum_boole,badCount]

lemma low_endpoint_bounds (K N : ℕ) :
    0 ≤ (∑ k ∈ lowBins K N,(endpoint k N:ℝ)) ∧
      (∑ k ∈ lowBins K N,(endpoint k N:ℝ)) ≤ 1 := by
  have he (k : ℕ) : (0:ℝ)≤endpoint k N := by exact_mod_cast endpoint_nonneg k N
  refine ⟨Finset.sum_nonneg (fun k _ => he k),?_⟩
  have hh : (∑ k ∈ lowBins K N,(endpoint k N:ℝ)) ≤
      ∑ k ∈ Finset.range (N+1),(endpoint k N:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k _ _ => he k)
  exact hh.trans (by exact_mod_cast (endpoint_sum_bounds N).2)

lemma low_bin_total_abs_le {B : ℝ} (hB : 0≤B) (K N : ℕ)
    (hb : ∀ k ∈ lowBins K N, |(bilinear k N:ℝ)|≤B*(2:ℝ)^k) :
    |(∑ k ∈ lowBins K N,∑ n ∈ Finset.range N,(kernel k n:ℝ))| ≤
      2*B*(N/K:ℕ)+1 := by
  have he (k : ℕ) : (∑ n ∈ Finset.range N,(kernel k n:ℝ)) =
      (bilinear k N:ℝ)+(endpoint k N:ℝ) := by exact_mod_cast kernel_total_eq_bilinear k N
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hE := low_endpoint_bounds K N
  have hsum : |(∑ k ∈ lowBins K N,(bilinear k N:ℝ))| ≤ 2*B*(N/K:ℕ) := by
    calc
      _ ≤ ∑ k ∈ lowBins K N, |(bilinear k N:ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ lowBins K N, B*(2:ℝ)^k := Finset.sum_le_sum hb
      _ = B*(∑ k ∈ lowBins K N,(2:ℝ)^k) := (Finset.mul_sum _ _ _).symm
      _ ≤ B*(2*(N/K:ℕ)) := mul_le_mul_of_nonneg_left (sum_low_scales K N) hB
      _ = _ := by ring
  have hh := abs_add_le (∑ k ∈ lowBins K N,(bilinear k N:ℝ))
    (∑ k ∈ lowBins K N,(endpoint k N:ℝ))
  rw [abs_of_nonneg hE.1] at hh
  linarith

/-- A finite estimate separating a signed low-bin estimate from an unsigned
  high-bin error. The hypothesis `hb` contains all the new cancellation needed. -/
theorem binned_mean_cropped_bound {B : ℝ} (hB : 0≤B) {K N : ℕ} (hK : 0<K) (hN : 0<N)
    (hb : ∀ k ∈ lowBins K N, |(bilinear k N:ℝ)|≤B*(2:ℝ)^k) :
    |mean (fun n => (binnedSign n:ℝ)) N| ≤
      2*B/(K:ℝ)+1/(N:ℝ)+badCount K N/N := by
  have he : (∑ n ∈ Finset.range N,(binnedSign n:ℝ)) =
      (∑ k ∈ lowBins K N,∑ n ∈ Finset.range N,(kernel k n:ℝ)) +
      (∑ k ∈ highBins K N,∑ n ∈ Finset.range N,(kernel k n:ℝ)) := by
    rw [lowBins,highBins,Finset.sum_filter_add_sum_filter_not,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    exact_mod_cast (sum_kernel (Finset.mem_range.mp hn)).symm
  have hlow := low_bin_total_abs_le hB K N hb
  have hhigh := high_bin_total_abs_le K N hK
  have htot : |(∑ n ∈ Finset.range N,(binnedSign n:ℝ))| ≤
      2*B*(N/K:ℕ)+1+badCount K N := by
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hlow hhigh)
  unfold mean
  rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  calc
    _ ≤ (2*B*(N/K:ℕ)+1+badCount K N)/(N:ℝ) :=
      div_le_div_of_nonneg_right htot (Nat.cast_nonneg N)
    _ ≤ (2*B*((N:ℝ)/K)+1+badCount K N)/(N:ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      gcongr
      exact Nat.cast_div_le
    _ = _ := by have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'; field_simp

/-- A subpower loss over the prime scale in every signed block suffices.
  This theorem does not prove the required uniform signed block estimate. -/
theorem density_half_of_subpower_block_bound (F : ℕ → ℕ)
    (hF : Tendsto F atTop atTop)
    (hlog : Tendsto (fun N => Real.log (F N:ℝ)/Real.log (N:ℝ)) atTop (𝓝 0))
    (hbound : ∀ᶠ N in atTop, ∀ k : ℕ, |(bilinear k N:ℝ)|≤(F N:ℝ)*(2:ℝ)^k) :
    {n | P n<P (n+1)}.HasDensity (1/2) := by
  let K : ℕ → ℕ := fun N => (F N)^2
  have hK : ∀ᶠ N in atTop, 0<K N := by
    filter_upwards [hF.eventually (eventually_gt_atTop 0)] with N hFN
    exact pow_pos hFN 2
  have hlogK : Tendsto (fun N => Real.log (K N:ℝ)/Real.log (N:ℝ)) atTop (𝓝 0) := by
    have hh := hlog.const_mul 2
    simpa only [K,Nat.cast_pow,Real.log_pow,Nat.cast_ofNat,mul_div_assoc,mul_zero] using hh
  have hbad := subpower_badCount_tendsto_zero K hK hlogK
  have hratio : Tendsto (fun N => 2*(F N:ℝ)/(K N:ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun N => 2*(1/(F N:ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_one_div_atTop_nhds_zero_nat.comp hF).const_mul (2:ℝ)
    apply hh.congr'
    filter_upwards [hF.eventually (eventually_gt_atTop 0)] with N hFN
    have hf : (F N:ℝ)≠0 := Nat.cast_ne_zero.mpr hFN.ne'
    simp only [K,Nat.cast_pow]
    field_simp
  have hu : Tendsto (fun N => 2*(F N:ℝ)/(K N:ℝ)+1/(N:ℝ)+badCount (K N) N/N) atTop (𝓝 0) := by
    simpa only [add_zero] using (hratio.add tendsto_one_div_atTop_nhds_zero_nat).add hbad
  apply density_half_iff_binned_mean_zero.mpr
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [hbound,hK,eventually_gt_atTop 0] with N hb hKN hN
    exact binned_mean_cropped_bound (Nat.cast_nonneg (F N)) hKN hN (fun k _ => hb k)

end Erdos371PrimeBinCriterion

#print axioms Erdos371PrimeBinCriterion.binned_mean_cropped_bound
#print axioms Erdos371PrimeBinCriterion.density_half_of_subpower_block_bound
