import FormalConjecturesUtil
import Submission.PrimeBinCriterion
import Submission.LogSmoothCount

/-! A balanced prime/cofactor sufficient bound for the signed bin sums.
  The bilinear cancellation hypothesis is not asserted unconditionally. -/

namespace Erdos371PrimeBinHybrid

open Finset Filter Erdos371PrimeBinKernel Erdos371PrimeBinBilinear Erdos371PrimeBinCriterion
open Erdos371PrimeDiscrepancy Erdos371SmallPrimeAveraging Erdos371CroppedEnergy
open Erdos371SubpowerCutoff
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def middleBins (K N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun k => K≤2^k ∧ 2^k≤N/K
noncomputable def outerBins (K N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun k => ¬(K≤2^k ∧ 2^k≤N/K)
noncomputable def smoothCount (K N : ℕ) : ℝ :=
  (((Finset.range N).filter fun n => P n≤2*K).card:ℝ)

lemma middle_scale_sum (K N : ℕ) :
    (∑ k ∈ middleBins K N,(2:ℝ)^k)≤2*(N/K:ℕ) := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)).trans (sum_low_scales K N)
  intro k hk
  obtain ⟨hk,hlo,hhi⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr ⟨hk,hhi⟩

lemma middle_reciprocal_sum {K : ℕ} (hK : 0<K) (N : ℕ) :
    (∑ k ∈ middleBins K N,1/(2:ℝ)^k) ≤ 4/(K:ℝ) := by
  let j := Nat.log 2 K
  have hsub : middleBins K N ⊆ Finset.Ico j (N+1) := by
    intro k hk
    obtain ⟨hk,hlo,hhi⟩ := Finset.mem_filter.mp hk
    have hjk := Nat.log_mono_right (b := 2) hlo
    rw [Nat.log_pow (by decide : 1<(2:ℕ))] at hjk
    exact Finset.mem_Ico.mpr ⟨hjk,Finset.mem_range.mp hk⟩
  have hKpow : (K:ℝ)≤2*(2:ℝ)^j := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1<(2:ℕ)) K
    have hh' : (K:ℝ)≤(2:ℝ)^(j+1) := by exact_mod_cast hh.le
    rw [pow_succ] at hh'
    linarith
  calc
    _ ≤ ∑ k ∈ Finset.Ico j (N+1),1/(2:ℝ)^k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (1/(2:ℝ)^j)*(∑ k ∈ Finset.range (N+1-j),(1/2:ℝ)^k) := by
      rw [Finset.sum_Ico_eq_sum_range,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_add,one_div_pow,one_div_mul_one_div]
    _ ≤ (1/(2:ℝ)^j)*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ ≤ 4/(K:ℝ) := by
      have hKr : (0:ℝ)<K := Nat.cast_pos.mpr hK
      apply (le_div_iff₀ hKr).mpr
      have hp : (0:ℝ)<(2:ℝ)^j := by positivity
      have hh := (div_le_iff₀ hp).mpr hKpow
      simp only [div_eq_mul_inv,one_mul] at hh ⊢
      nlinarith

lemma outer_kernel_abs {K N n : ℕ} (hK : 0<K) (hn : n<N) :
    |∑ k ∈ outerBins K N,(kernel k n:ℝ)| ≤
      (if P n≤2*K then 1 else 0) +
        (if n/P n≤K ∨ (n+1)/P (n+1)≤K then 1 else 0) := by
  simp only [kernel_eq_single,Int.cast_ite,Int.cast_zero,Finset.sum_ite_eq']
  by_cases hi : index n∈outerBins K N
  · simp only [if_pos hi]
    by_cases hz : binnedSign n=0
    · simp only [hz,Int.cast_zero,abs_zero]
      split_ifs <;> norm_num
    · have hs := kernel_support hz
      obtain ⟨_,hlo,hhi⟩ := Erdos371PrimeHarmonicBlocks.mem_block.mp hs
      have hh := (Finset.mem_filter.mp hi).2
      have habs : |(binnedSign n:ℝ)|≤1 := by exact_mod_cast kernel_abs_le_one (index n) n
      by_cases hlow : 2^(index n)<K
      · have hp : P n≤2*K := by
          have hpn : P n≤winner n := le_max_left _ _
          rw [pow_succ] at hhi
          omega
        rw [if_pos hp]
        split_ifs <;> linarith
      · have hb := high_winner_bad hK hn (by omega : N/K<winner n)
        rw [if_pos hb]
        split_ifs <;> linarith
  · simp only [if_neg hi,abs_zero]
    split_ifs <;> norm_num

lemma outer_total_abs_le {K : ℕ} (hK : 0<K) (N : ℕ) :
    |∑ k ∈ outerBins K N,∑ n ∈ Finset.range N,(kernel k n:ℝ)| ≤
      smoothCount K N+badCount K N := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ n ∈ Finset.range N,|∑ k ∈ outerBins K N,(kernel k n:ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N,((if P n≤2*K then (1:ℝ) else 0)+
        (if n/P n≤K ∨ (n+1)/P (n+1)≤K then 1 else 0)) :=
      Finset.sum_le_sum (fun n hn => outer_kernel_abs hK (Finset.mem_range.mp hn))
    _ = _ := by simp [Finset.sum_add_distrib,smoothCount,badCount]

lemma middle_endpoint_bounds (K N : ℕ) :
    0≤(∑ k ∈ middleBins K N,(endpoint k N:ℝ)) ∧
      (∑ k ∈ middleBins K N,(endpoint k N:ℝ))≤1 := by
  have hnonneg (k : ℕ) : (0:ℝ)≤endpoint k N := by exact_mod_cast endpoint_nonneg k N
  refine ⟨Finset.sum_nonneg (fun k _ => hnonneg k),?_⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun k _ _ => hnonneg k)).trans (by exact_mod_cast (endpoint_sum_bounds N).2)

lemma middle_total_abs_le {B : ℝ} (hB : 0≤B) {K : ℕ} (hK : 0<K) (N : ℕ)
    (hb : ∀ k ∈ middleBins K N, |(bilinear k N:ℝ)|≤B*((2:ℝ)^k+N/(2:ℝ)^k)) :
    |∑ k ∈ middleBins K N,∑ n ∈ Finset.range N,(kernel k n:ℝ)| ≤
      6*B*N/(K:ℝ)+1 := by
  have he (k : ℕ) : (∑ n ∈ Finset.range N,(kernel k n:ℝ)) =
      (bilinear k N:ℝ)+(endpoint k N:ℝ) := by exact_mod_cast kernel_total_eq_bilinear k N
  have hsum : |∑ k ∈ middleBins K N,(bilinear k N:ℝ)|≤6*B*N/(K:ℝ) := by
    calc
      _ ≤ ∑ k ∈ middleBins K N,|(bilinear k N:ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ middleBins K N,B*((2:ℝ)^k+N/(2:ℝ)^k) := Finset.sum_le_sum hb
      _ = B*((∑ k ∈ middleBins K N,(2:ℝ)^k)+(N:ℝ)*∑ k ∈ middleBins K N,1/(2:ℝ)^k) := by
        simp [Finset.mul_sum,mul_add,Finset.sum_add_distrib,div_eq_mul_inv]
      _ ≤ B*(2*(N/K:ℕ)+(N:ℝ)*(4/(K:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact add_le_add (middle_scale_sum K N)
          (mul_le_mul_of_nonneg_left (middle_reciprocal_sum hK N) (by positivity))
      _ ≤ B*(2*((N:ℝ)/K)+(N:ℝ)*(4/(K:ℝ))) := by gcongr; exact Nat.cast_div_le
      _ = _ := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hE := middle_endpoint_bounds K N
  have hh := abs_add_le (∑ k ∈ middleBins K N,(bilinear k N:ℝ))
    (∑ k ∈ middleBins K N,(endpoint k N:ℝ))
  rw [abs_of_nonneg hE.1] at hh
  linarith

/-- A finite two-sided cropping estimate. Only the middle signed blocks
  need the stated hybrid estimate; the two outer ranges are handled by counts. -/
theorem binned_mean_hybrid_bound {B : ℝ} (hB : 0≤B) {K N : ℕ} (hK : 0<K) (hN : 0<N)
    (hb : ∀ k ∈ middleBins K N, |(bilinear k N:ℝ)|≤B*((2:ℝ)^k+N/(2:ℝ)^k)) :
    |mean (fun n => (binnedSign n:ℝ)) N| ≤
      6*B/(K:ℝ)+1/(N:ℝ)+smoothCount K N/N+badCount K N/N := by
  have he : (∑ n ∈ Finset.range N,(binnedSign n:ℝ)) =
      (∑ k ∈ middleBins K N,∑ n ∈ Finset.range N,(kernel k n:ℝ))+
      (∑ k ∈ outerBins K N,∑ n ∈ Finset.range N,(kernel k n:ℝ)) := by
    rw [middleBins,outerBins,Finset.sum_filter_add_sum_filter_not,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    exact_mod_cast (sum_kernel (Finset.mem_range.mp hn)).symm
  have hm := middle_total_abs_le hB hK N hb
  have ho := outer_total_abs_le hK N
  have htot : |∑ n ∈ Finset.range N,(binnedSign n:ℝ)| ≤
      6*B*N/(K:ℝ)+1+(smoothCount K N+badCount K N) := by
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hm ho)
  unfold mean
  rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  calc
    _ ≤ (6*B*N/(K:ℝ)+1+(smoothCount K N+badCount K N))/(N:ℝ) :=
      div_le_div_of_nonneg_right htot (Nat.cast_nonneg N)
    _ = _ := by have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'; field_simp; ring

lemma subpower_smoothCount_tendsto_zero (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop,0<K N)
    (hlog : Tendsto (fun N => Real.log (K N:ℝ)/Real.log (N:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => smoothCount (K N) N/N) atTop (𝓝 0) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun N : ℕ => Real.log 2/Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero.comp hlogN).const_mul (Real.log 2)
  have hL : Tendsto (fun N => Real.log ((2*K N:ℕ):ℝ)/Real.log (N:ℝ)) atTop (𝓝 0) := by
    have hh := hconst.add hlog
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [hK] with N hKN
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num)
      (Nat.cast_ne_zero.mpr hKN.ne'),add_div]
  have hpos : ∀ᶠ N in atTop,0<2*K N := hK.mono (fun N hN => by omega)
  simpa only [smoothCount] using
    Erdos371LogSmoothCount.moving_smooth_count_tendsto_zero (fun N => 2*K N) hpos hL

/-- A balanced signed estimate with a subpower loss is sufficient. It is
  a hypothesis here, not a consequence of the preceding unsigned sieve. -/
theorem density_half_of_subpower_hybrid_bound (F : ℕ → ℕ)
    (hF : Tendsto F atTop atTop)
    (hlog : Tendsto (fun N => Real.log (F N:ℝ)/Real.log (N:ℝ)) atTop (𝓝 0))
    (hbound : ∀ᶠ N in atTop,∀ k : ℕ,
      |(bilinear k N:ℝ)|≤(F N:ℝ)*((2:ℝ)^k+N/(2:ℝ)^k)) :
    {n | P n<P (n+1)}.HasDensity (1/2) := by
  let K : ℕ → ℕ := fun N => (F N)^2
  have hK : ∀ᶠ N in atTop,0<K N := by
    filter_upwards [hF.eventually (eventually_gt_atTop 0)] with N hFN
    exact pow_pos hFN 2
  have hlogK : Tendsto (fun N => Real.log (K N:ℝ)/Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa only [K,Nat.cast_pow,Real.log_pow,Nat.cast_ofNat,mul_div_assoc,mul_zero] using hlog.const_mul 2
  have hbad := subpower_badCount_tendsto_zero K hK hlogK
  have hsmooth := subpower_smoothCount_tendsto_zero K hK hlogK
  have hratio : Tendsto (fun N => 6*(F N:ℝ)/(K N:ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun N => 6*(1/(F N:ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_one_div_atTop_nhds_zero_nat.comp hF).const_mul (6:ℝ)
    apply hh.congr'
    filter_upwards [hF.eventually (eventually_gt_atTop 0)] with N hFN
    have hf : (F N:ℝ)≠0 := Nat.cast_ne_zero.mpr hFN.ne'
    simp only [K,Nat.cast_pow]
    field_simp
  have hu : Tendsto (fun N => 6*(F N:ℝ)/(K N:ℝ)+1/(N:ℝ)+smoothCount (K N) N/N+badCount (K N) N/N)
      atTop (𝓝 0) := by
    simpa only [add_zero] using ((hratio.add tendsto_one_div_atTop_nhds_zero_nat).add hsmooth).add hbad
  apply density_half_iff_binned_mean_zero.mpr
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [hbound,hK,eventually_gt_atTop 0] with N hb hKN hN
    exact binned_mean_hybrid_bound (Nat.cast_nonneg (F N)) hKN hN (fun k _ => hb k)

end Erdos371PrimeBinHybrid

#print axioms Erdos371PrimeBinHybrid.binned_mean_hybrid_bound
#print axioms Erdos371PrimeBinHybrid.density_half_of_subpower_hybrid_bound
