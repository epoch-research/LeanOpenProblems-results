import Submission.SmoothCutoffSkew
import Submission.ClippedLogCriterion

/-! A sufficient arithmetic reciprocity criterion, expressed entirely using
adjacent rational-power smoothness cutoffs. The reciprocity hypothesis is not
proved; it can be attacked through the band kernels in SmoothCutoffSkew. -/

namespace Erdos371
open Finset Filter
open FiniteSieve

noncomputable def thresholdBit (a i : ℕ) : ℝ := if a ≤ i then 1 else 0
noncomputable def orderedGridSkew (M a b : ℕ) : ℝ :=
  ∑ i ∈ range M, (thresholdBit a i*thresholdBit b (i+1)-thresholdBit a (i+1)*thresholdBit b i)
noncomputable def threeWaySign (a b : ℕ) : ℝ := if a < b then 1 else if b < a then -1 else 0

lemma orderedGridSkew_swap (M a b : ℕ) : orderedGridSkew M b a = -orderedGridSkew M a b := by
  unfold orderedGridSkew
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  ring

lemma orderedGridSkew_of_lt (M a b : ℕ) (hab : a < b) (hb : b ≤ M) : orderedGridSkew M a b = 1 := by
  have he (i : ℕ) : thresholdBit a i*thresholdBit b (i+1)-thresholdBit a (i+1)*thresholdBit b i =
      if i = b-1 then (1 : ℝ) else 0 := by
    unfold thresholdBit
    split_ifs <;> norm_num <;> omega
  unfold orderedGridSkew
  simp_rw [he]
  rw [sum_ite_eq']
  simp [mem_range,show b-1 < M by omega]

lemma orderedGridSkew_eq (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M) :
    orderedGridSkew M a b = threeWaySign a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [orderedGridSkew_of_lt M a b h hb]
    simp [threeWaySign,h]
  · subst b
    simp [orderedGridSkew,threeWaySign,mul_comm]
  · rw [orderedGridSkew_swap,orderedGridSkew_of_lt M b a h ha]
    simp [threeWaySign,h,h.not_gt]

noncomputable def powerGridLabel (M N n : ℕ) : ℕ := ⌈(M : ℝ)*normalizedPrimeLog N n⌉₊
noncomputable def powerGridSign (M N n : ℕ) : ℝ :=
  orderedGridSkew M (powerGridLabel M N n) (powerGridLabel M N (n+1))
noncomputable def powerGridCutoff (M N i : ℕ) : ℕ := ⌊(N : ℝ)^((i : ℝ)/M)⌋₊

lemma normalizedPrimeLog_le_iff (N n : ℕ) (u : ℝ) (hN : 1 < N) (hu : 0 ≤ u) :
    normalizedPrimeLog N n ≤ u ↔ (Nat.maxPrimeFac n : ℝ) ≤ (N : ℝ)^u := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  by_cases hn : n = 0
  · subst n
    simp [normalizedPrimeLog,hu,Real.rpow_nonneg hN0.le]
  · have hp : (0 : ℝ) < Nat.maxPrimeFac n := by exact_mod_cast maxPrimeFac_pos_of_pos n (by omega)
    unfold normalizedPrimeLog primeLog
    rw [div_le_iff₀ hlog,← Real.log_rpow hN0,Real.log_le_log_iff hp (Real.rpow_pos_of_pos hN0 u)]

lemma powerGridLabel_le_iff (M N n i : ℕ) (hM : 0 < M) (hN : 1 < N) :
    powerGridLabel M N n ≤ i ↔ Nat.maxPrimeFac n ≤ powerGridCutoff M N i := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  unfold powerGridLabel powerGridCutoff
  rw [Nat.ceil_le,mul_comm (M : ℝ),← le_div_iff₀ hm]
  rw [normalizedPrimeLog_le_iff N n ((i : ℝ)/M) hN (by positivity)]
  exact (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) _)).symm

lemma powerGridLabel_le (M N n : ℕ) (hN : 1 < N) (hn : n ≤ N) : powerGridLabel M N n ≤ M := by
  apply Nat.ceil_le.mpr
  have h := (normalizedPrimeLog_mem_unit N n hN hn).2
  have hm := Nat.cast_nonneg (α := ℝ) M
  nlinarith

lemma equal_powerGridLabel_near (M N n : ℕ) (hM : 0 < M) (hN : 1 < N) (hn : n < N)
    (he : powerGridLabel M N n = powerGridLabel M N (n+1)) :
    |logDifference N n| ≤ 1/(M : ℝ) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hx := (normalizedPrimeLog_mem_unit N n hN hn.le).1
  have hy := (normalizedPrimeLog_mem_unit N (n+1) hN (by omega)).1
  have ha := Nat.le_ceil ((M : ℝ)*normalizedPrimeLog N n)
  have hb := Nat.le_ceil ((M : ℝ)*normalizedPrimeLog N (n+1))
  have hc := Nat.ceil_lt_add_one (mul_nonneg hm.le hx)
  have hd := Nat.ceil_lt_add_one (mul_nonneg hm.le hy)
  change powerGridLabel M N n = powerGridLabel M N (n+1) at he
  change (M : ℝ)*normalizedPrimeLog N n ≤ (powerGridLabel M N n : ℝ) at ha
  change (M : ℝ)*normalizedPrimeLog N (n+1) ≤ (powerGridLabel M N (n+1) : ℝ) at hb
  change (powerGridLabel M N n : ℝ) < (M : ℝ)*normalizedPrimeLog N n+1 at hc
  change (powerGridLabel M N (n+1) : ℝ) < (M : ℝ)*normalizedPrimeLog N (n+1)+1 at hd
  rw [he] at ha hc
  rw [logDifference_eq_sub,abs_le]
  constructor
  · have h : normalizedPrimeLog N n-normalizedPrimeLog N (n+1) ≤ 1/(M : ℝ) :=
      (le_div_iff₀ hm).mpr (by nlinarith)
    linarith
  · exact (le_div_iff₀ hm).mpr (by nlinarith)

lemma powerGridSign_eq_of_not_near (M N n : ℕ) (δ : ℝ)
    (hM : 0 < M) (hN : 1 < N) (hn : n < N) (hn0 : 0 < n) (hwidth : 1/(M : ℝ) ≤ δ)
    (hnear : ¬ logRatioEvent N δ n) : powerGridSign M N n = factorSign n := by
  have hne : powerGridLabel M N n ≠ powerGridLabel M N (n+1) := by
    intro he
    exact hnear ((logRatioEvent_iff_logDifference N n δ hN hn0).mpr
      ((equal_powerGridLabel_near M N n hM hN hn he).trans hwidth))
  unfold powerGridSign
  rw [orderedGridSkew_eq M _ _ (powerGridLabel_le M N n hN hn.le)
    (powerGridLabel_le M N (n+1) hN (by omega))]
  have hm := Nat.cast_nonneg (α := ℝ) M
  unfold factorSign predicateSign
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · rw [if_pos h]
    have hl : normalizedPrimeLog N n ≤ normalizedPrimeLog N (n+1) := by
      have hd := (logDifference_pos_iff N n hN hn0).mpr h
      rw [logDifference_eq_sub] at hd
      linarith
    have hc : powerGridLabel M N n ≤ powerGridLabel M N (n+1) :=
      Nat.ceil_mono (mul_le_mul_of_nonneg_left hl hm)
    simp [threeWaySign,lt_of_le_of_ne hc hne]
  · rw [if_neg h]
    have hl : normalizedPrimeLog N (n+1) ≤ normalizedPrimeLog N n := by
      have hd : logDifference N n ≤ 0 := not_lt.mp (fun h' => h ((logDifference_pos_iff N n hN hn0).mp h'))
      rw [logDifference_eq_sub] at hd
      linarith
    have hc : powerGridLabel M N (n+1) ≤ powerGridLabel M N n :=
      Nat.ceil_mono (mul_le_mul_of_nonneg_left hl hm)
    have hh := lt_of_le_of_ne hc hne.symm
    simp [threeWaySign,hh,hh.not_gt]

lemma powerGridSign_error_le_two (M N n : ℕ) (hN : 1 < N) (hn : n < N) :
    |factorSign n-powerGridSign M N n| ≤ 2 := by
  unfold powerGridSign
  rw [orderedGridSkew_eq M _ _ (powerGridLabel_le M N n hN hn.le)
    (powerGridLabel_le M N (n+1) hN (by omega))]
  unfold threeWaySign factorSign predicateSign
  split_ifs <;> norm_num

lemma powerGridSign_error_sum_bound (M N : ℕ) (δ : ℝ) (hM : 0 < M) (hN : 1 < N)
    (hwidth : 1/(M : ℝ) ≤ δ) :
    (∑ n ∈ range N, |factorSign n-powerGridSign M N n|) ≤ 2+2*((logRatioSet N δ).card : ℝ) := by
  classical
  have hterm (n : ℕ) (hn : n ∈ range N) : |factorSign n-powerGridSign M N n| ≤
      (if n = 0 then (2 : ℝ) else 0)+(if logRatioEvent N δ n then (2 : ℝ) else 0) := by
    by_cases hn0 : n = 0
    · rw [if_pos hn0]
      exact (powerGridSign_error_le_two M N n hN (mem_range.mp hn)).trans
        (le_add_of_nonneg_right (by split_ifs <;> norm_num))
    · rw [if_neg hn0,zero_add]
      by_cases hnear : logRatioEvent N δ n
      · rw [if_pos hnear]; exact powerGridSign_error_le_two M N n hN (mem_range.mp hn)
      · rw [if_neg hnear,powerGridSign_eq_of_not_near M N n δ hM hN (mem_range.mp hn) (by omega) hwidth hnear,
          sub_self,abs_zero]
  have hs := sum_le_sum hterm
  simpa only [sum_add_distrib,sum_ite_eq',mem_range,show 0 < N by omega,if_true,
    sum_ite,sum_const_zero,add_zero,sum_const,nsmul_eq_mul,logRatioSet,mul_comm] using hs

lemma powerGridSign_uniform_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, |factorSign n-powerGridSign M N n|)/N ≤ ε := by
  obtain ⟨δ,hδ,hr⟩ := logRatioSet_uniform_rarity (ε/4) (by positivity)
  obtain ⟨M,hM⟩ := exists_nat_gt (1/δ)
  have hM0 : 0 < M := by have : (0 : ℝ) < M := (by positivity : (0 : ℝ) < 1/δ).trans hM; exact_mod_cast this
  have hm : (0 : ℝ) < M := by exact_mod_cast hM0
  have hw : 1/(M : ℝ) ≤ δ := by
    apply (div_le_iff₀ hm).mpr
    have h := (div_lt_iff₀ hδ).mp hM
    linarith
  refine ⟨M,hM0,?_⟩
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  filter_upwards [hr,ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2),
    eventually_gt_atTop (1 : ℕ)] with N hr ht hN
  have hb := div_le_div_of_nonneg_right (powerGridSign_error_sum_bound M N δ hM0 hN hw) (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div,mul_div_assoc] at hb
  linarith

noncomputable def smoothGridPoint (M N n : ℕ) : ℝ :=
  ∑ i ∈ range M, (smoothIndicator (powerGridCutoff M N i) n*smoothIndicator (powerGridCutoff M N (i+1)) (n+1)-
    smoothIndicator (powerGridCutoff M N (i+1)) n*smoothIndicator (powerGridCutoff M N i) (n+1))

lemma powerGridSign_eq_smoothGridPoint (M N n : ℕ) (hM : 0 < M) (hN : 1 < N) :
    powerGridSign M N n = smoothGridPoint M N n := by
  unfold powerGridSign orderedGridSkew smoothGridPoint thresholdBit smoothIndicator
  simp_rw [powerGridLabel_le_iff M N _ _ hM hN]

lemma smoothGridPoint_abs_le (M N n : ℕ) : |smoothGridPoint M N n| ≤ M := by
  have ht (B C k : ℕ) : |smoothIndicator B k*smoothIndicator C (k+1)-smoothIndicator C k*smoothIndicator B (k+1)| ≤ 1 := by
    unfold smoothIndicator
    split_ifs <;> norm_num
  calc
    _ ≤ ∑ i ∈ range M, |smoothIndicator (powerGridCutoff M N i) n*smoothIndicator (powerGridCutoff M N (i+1)) (n+1)-
        smoothIndicator (powerGridCutoff M N (i+1)) n*smoothIndicator (powerGridCutoff M N i) (n+1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range M, (1 : ℝ) := sum_le_sum (fun i hi => ht _ _ _)
    _ = _ := by simp

lemma smoothGridPoint_shift_sum (M N : ℕ) :
    (∑ n ∈ range N, smoothGridPoint M N (n+1)) =
      ∑ i ∈ range M, smoothCutoffSkew (powerGridCutoff M N i) (powerGridCutoff M N (i+1)) N := by
  unfold smoothGridPoint smoothCutoffSkew
  rw [sum_comm]

lemma smoothGridPoint_boundary_tendsto_zero (M : ℕ) :
    Tendsto (fun N : ℕ => ((∑ n ∈ range N, smoothGridPoint M N n)-
      (∑ n ∈ range N, smoothGridPoint M N (n+1)))/N) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_const_div_atTop_nhds_zero_nat (2*(M : ℝ)))
  intro N
  rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N),← sum_sub_distrib,sum_range_sub']
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact (abs_sub _ _).trans (by have := smoothGridPoint_abs_le M N 0; have := smoothGridPoint_abs_le M N N; linarith)

/-- Reciprocity for adjacent power cutoffs suffices. This is strictly a
conditional theorem: no such reciprocity limit is supplied by this file. -/
theorem density_of_power_smooth_reciprocity
    (hrec : ∀ M : ℕ, 0 < M → ∀ i ∈ range M,
      Tendsto (fun N : ℕ => smoothCutoffSkew (powerGridCutoff M N i) (powerGridCutoff M N (i+1)) N/N)
        atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) := by
  have hg (M : ℕ) (hM : 0 < M) : Tendsto (fun N : ℕ => (∑ n ∈ range N, powerGridSign M N n)/N) atTop (nhds 0) := by
    have hs := tendsto_finset_sum (range M) (hrec M hM)
    simp only [sum_const_zero] at hs
    have hs' : Tendsto (fun N : ℕ => (∑ n ∈ range N, smoothGridPoint M N (n+1))/N) atTop (nhds 0) := by
      simpa only [smoothGridPoint_shift_sum,sum_div] using hs
    have ht := (smoothGridPoint_boundary_tendsto_zero M).add hs'
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    simp_rw [powerGridSign_eq_smoothGridPoint M N _ hM hN]
    ring
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_count_difference]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M,hM,ha⟩ := powerGridSign_uniform_approximation (ε/2) (by positivity)
  have hs := (Metric.tendsto_nhds.mp (hg M hM)) (ε/2) (by positivity)
  filter_upwards [ha,hs] with N ha hs
  rw [Real.dist_eq,sub_zero] at hs ⊢
  have hd : |(∑ n ∈ range N, factorSign n)/N-(∑ n ∈ range N, powerGridSign M N n)/N| ≤ ε/2 := by
    apply le_trans _ ha
    rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
  have ht := abs_sub ((∑ n ∈ range N, factorSign n)/N-(∑ n ∈ range N, powerGridSign M N n)/N)
    (-((∑ n ∈ range N, powerGridSign M N n)/N))
  simp only [sub_neg_eq_add,sub_add_cancel,abs_neg] at ht
  linarith

#print axioms density_of_power_smooth_reciprocity
end Erdos371
