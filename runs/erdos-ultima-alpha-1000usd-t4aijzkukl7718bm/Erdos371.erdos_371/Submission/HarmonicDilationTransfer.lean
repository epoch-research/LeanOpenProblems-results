import Submission.FiniteEndpointTransfer

/-! Harmonic endpoint and dilation identities. The shorter endpoint is kept
in the exact formula, then removed with an explicit logarithmic error. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def logPrefixMean (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Icc 1 N, F n/(n : ℝ))/Real.log N

lemma sum_divisible_Icc (p N : ℕ) (hp : 0 < p) (F : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, if p ∣ n then F n else 0) =
      ∑ m ∈ Icc 1 (N/p), F (p*m) := by
  rw [← sum_filter]
  symm
  apply sum_nbij' (fun m => p*m) (fun n => n/p)
  · intro m hm
    obtain ⟨hm1,hmN⟩ := mem_Icc.mp hm
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith,?_⟩,dvd_mul_right p m⟩
    exact (Nat.mul_le_mul_left p hmN).trans (Nat.mul_div_le N p)
  · intro n hn
    obtain ⟨hn,hd⟩ := mem_filter.mp hn
    obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp,Nat.div_le_div_right hnN⟩
  · intro m hm
    exact Nat.mul_div_right m hp
  · intro n hn
    exact Nat.mul_div_cancel' (mem_filter.mp hn).2
  · intro m hm
    rfl

lemma harmonic_dilation_sum (p N : ℕ) (hp : 0 < p) (F : ℕ → ℝ) :
    p*(∑ n ∈ Icc 1 N, if p ∣ n then F n/(n : ℝ) else 0) =
      ∑ m ∈ Icc 1 (N/p), F (p*m)/(m : ℝ) := by
  rw [sum_divisible_Icc p N hp,mul_sum]
  apply sum_congr rfl
  intro m hm
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Nat.cast_mul]
  field_simp

lemma harmonic_endpoint_bound (M N : ℕ) (hMN : M ≤ N) (F : ℕ → ℝ)
    (hF : ∀ n, |F n| ≤ 1) :
    |(∑ n ∈ Icc 1 N, F n/(n : ℝ))-(∑ n ∈ Icc 1 M, F n/(n : ℝ))| ≤
      (N : ℝ)/(M+1 : ℝ) := by
  have hsub : Icc 1 M ⊆ Icc 1 N := Icc_subset_Icc le_rfl hMN
  rw [← sum_sdiff_eq_sub hsub]
  calc
    _ ≤ ∑ n ∈ Icc 1 N \ Icc 1 M, |F n/(n : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Icc 1 N \ Icc 1 M, (1 : ℝ)/(M+1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hn,hnot⟩ := mem_sdiff.mp hn
      obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
      have hMn : M+1 ≤ n := by simp only [mem_Icc] at hnot; omega
      have hab : |(n : ℝ)|=(n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
      rw [abs_div,hab]
      exact (div_le_div_of_nonneg_right (hF n) (Nat.cast_nonneg n)).trans
        (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hMn))
    _ ≤ _ := by
      rw [sum_const,nsmul_eq_mul,mul_one_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hc : (Icc 1 N \ Icc 1 M).card ≤ (Icc 1 N).card := card_le_card sdiff_subset
      rw [Nat.card_Icc] at hc
      exact_mod_cast (show (Icc 1 N \ Icc 1 M).card ≤ N by omega)

/-- The harmonic mass between N/p and N is uniformly bounded for fixed p. -/
lemma harmonic_div_endpoint_bound (p N : ℕ) (hp : 0 < p) (F : ℕ → ℝ)
    (hF : ∀ n, |F n| ≤ 1) :
    |(∑ n ∈ Icc 1 N, F n/(n : ℝ))-(∑ n ∈ Icc 1 (N/p), F n/(n : ℝ))| ≤ p := by
  have hb := harmonic_endpoint_bound (N/p) N (Nat.div_le_self N p) F hF
  have hsize : (N : ℝ) ≤ p*((N/p : ℕ)+1 : ℝ) := by
    exact_mod_cast (Nat.lt_mul_div_succ N hp).le
  exact hb.trans ((div_le_iff₀ (by positivity : (0 : ℝ)<(N/p : ℕ)+1)).mpr hsize)

noncomputable def logConditionedGap {A : Type*} (N p : ℕ) (L : ℕ → A)
    (C : A → A → ℝ) : ℝ :=
  p*logPrefixMean N (fun n => if p ∣ n then C (L n) (L (n+p)) else 0)

/-- Exact conditioned harmonic dilation. Both sums use the SAME log N
normalizer; the shorter sum is not renormalized at N/p. -/
lemma logConditionedGap_dilation {A : Type*} (N p : ℕ) (hp : 0 < p)
    (L : ℕ → A) (C : A → A → ℝ) (hL : ∀ m, 0 < m → L (p*m)=L m) :
    logConditionedGap N p L C =
      (∑ m ∈ Icc 1 (N/p), C (L m) (L (m+1))/(m : ℝ))/Real.log N := by
  unfold logConditionedGap logPrefixMean
  simp only [ite_div,zero_div]
  rw [← mul_div_assoc,harmonic_dilation_sum p N hp]
  congr 1
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  rw [hL m hm0,show p*m+p=p*(m+1) by ring,hL (m+1) (by omega)]

/-- For logarithmic averages the fixed-multiplier endpoint loss vanishes.
This does NOT make the same replacement valid for natural averages. -/
theorem logConditionedGap_adjacent_bound {A : Type*} (N p : ℕ) (hN : 1 < N) (hp : 0 < p)
    (L : ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1)
    (hL : ∀ m, 0 < m → L (p*m)=L m) :
    |logConditionedGap N p L C-logPrefixMean N (fun m => C (L m) (L (m+1)))| ≤
      p/Real.log N := by
  rw [logConditionedGap_dilation N p hp L C hL,logPrefixMean,← sub_div,abs_div,
    abs_of_pos (Real.log_pos (by exact_mod_cast hN)),abs_sub_comm]
  exact div_le_div_of_nonneg_right
    (harmonic_div_endpoint_bound p N hp (fun m => C (L m) (L (m+1))) (fun m => hC _ _))
    (Real.log_pos (by exact_mod_cast hN)).le

theorem logConditionedGap_adjacent_error_zero {A : Type*} (p : ℕ) (hp : 0 < p)
    (L : ℕ → ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1)
    (hL : ∀ᶠ N : ℕ in atTop, ∀ m, 0 < m → L N (p*m)=L N m) :
    Tendsto (fun N : ℕ => logConditionedGap N p (L N) C-
      logPrefixMean N (fun m => C (L N m) (L N (m+1)))) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => (p : ℝ)/Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' _ ht
  filter_upwards [hL,eventually_gt_atTop (1 : ℕ)] with N hLN hN
  simpa only [Real.norm_eq_abs] using logConditionedGap_adjacent_bound N p hN hp (L N) C hC hLN

#print axioms harmonic_div_endpoint_bound
#print axioms logConditionedGap_adjacent_error_zero
end Erdos371.FiniteInformation
