import Submission.ExponentialTauberian

/-! The Abelian converse to the bounded exponential Tauberian theorem.
All cancellation assertions in this file are generic implications; no
unproved arithmetic cancellation is used as a lemma. -/
namespace Erdos371.ExponentialWindow
open Finset Filter
open scoped Topology

noncomputable def partialSum (f : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ range N, f n

lemma prefix_abs_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (N : ℕ) :
    |partialSum f N| ≤ N := by
  calc
    _ ≤ ∑ n ∈ range N, |f n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ range N, (1 : ℝ) := sum_le_sum (fun n _ => hf n)
    _ = _ := by simp

lemma hasSum_succ_geometric {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => (n+1 : ℝ)*r^n) (((1-r)⁻¹)^2) := by
  have hnorm : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using hr1
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_lt_one hr hr1)
  convert h using 1
  · ext n
    ring
  · field_simp
    ring

lemma summable_prefix_geometric (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => partialSum f (n+1)*r^n) ∧
      Summable (fun n : ℕ => partialSum f n*r^n) := by
  have hnorm : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using hr1
  constructor
  · apply Summable.of_norm_bounded (hasSum_succ_geometric hr hr1).summable
    intro n
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr n)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast prefix_abs_le f hf (n+1)) (pow_nonneg hr n)
  · apply Summable.of_norm_bounded (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
    intro n
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr n)]
    exact mul_le_mul_of_nonneg_right (prefix_abs_le f hf n) (pow_nonneg hr n)

lemma weighted_prefix_identity (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, f n*r^n) = (1-r)*∑' n : ℕ, partialSum f (n+1)*r^n := by
  obtain ⟨hA,hB⟩ := summable_prefix_geometric f hf hr hr1
  have hd (n : ℕ) : f n*r^n = partialSum f (n+1)*r^n-partialSum f n*r^n := by
    simp only [partialSum, sum_range_succ]
    ring
  have hb : (∑' n : ℕ, partialSum f n*r^n) = r*∑' n : ℕ, partialSum f (n+1)*r^n := by
    rw [hB.tsum_eq_zero_add]
    simp only [partialSum, sum_range_zero, zero_mul, zero_add, pow_succ]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  simp_rw [hd]
  rw [hA.tsum_sub hB, hb]
  ring

lemma geometric_mean_affine_bound (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {r C ε : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hprefix : ∀ N : ℕ, |partialSum f N| ≤ C+ε*N) :
    |∑' n : ℕ, f n*r^n| ≤ C+ε/(1-r) := by
  have hg : HasSum (fun n : ℕ => (C+ε*(n+1))*r^n)
      (C*(1-r)⁻¹+ε*((1-r)⁻¹)^2) := by
    convert ((hasSum_geometric_of_lt_one hr hr1).mul_left C).add
      ((hasSum_succ_geometric hr hr1).mul_left ε) using 1
    ext n
    ring
  have hb (n : ℕ) : ‖partialSum f (n+1)*r^n‖ ≤ (C+ε*(n+1))*r^n := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr n)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hprefix (n+1)) (pow_nonneg hr n)
  have hs := tsum_of_norm_bounded hg hb
  rw [weighted_prefix_identity f hf hr hr1, abs_mul, abs_of_pos (sub_pos.mpr hr1)]
  calc
    _ ≤ (1-r)*(C*(1-r)⁻¹+ε*((1-r)⁻¹)^2) := by
      rw [← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hr1.le)
    _ = _ := by field_simp [(sub_pos.mpr hr1).ne']

/-- A quantitative Abelian estimate from a uniform affine prefix bound. -/
theorem exponential_mean_affine_bound (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {C ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t)
    (hprefix : ∀ N : ℕ, |partialSum f N| ≤ C+ε*N) :
    |exponentialMean f t| ≤ C*t+ε*(1+t) := by
  have hr : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he (n : ℕ) : Real.exp (-t*n) = (Real.exp (-t))^n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [exponentialMean, he, abs_mul, abs_of_pos ht]
  calc
    _ ≤ t*(C+ε/(1-Real.exp (-t))) := mul_le_mul_of_nonneg_left
      (geometric_mean_affine_bound f hf hr hr1 hprefix) ht.le
    _ = C*t+ε*(t*(1-Real.exp (-t))⁻¹) := by ring
    _ ≤ C*t+ε*(t*(1+t⁻¹)) := by
      gcongr
      exact exp_inverse_gap_bound ht
    _ = _ := by rw [mul_add, mul_one, mul_inv_cancel₀ ht.ne']; ring

lemma exists_affine_prefix_bound (f : ℕ → ℝ)
    (hmean : Tendsto (fun N : ℕ => partialSum f N/N) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |partialSum f N| ≤ C+ε*N := by
  have he := (Metric.tendsto_nhds.mp hmean) ε hε
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  let C : ℝ := ∑ n ∈ range K, |partialSum f n|
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C,hC,?_⟩
  intro N
  by_cases hNK : N < K
  · have hb : |partialSum f N| ≤ C := single_le_sum (fun n _ => abs_nonneg (partialSum f n)) (mem_range.mpr hNK)
    exact hb.trans (le_add_of_nonneg_right (mul_nonneg hε.le (Nat.cast_nonneg N)))
  · by_cases hN : N = 0
    · simp [hN, partialSum, hC]
    · have heN := hK N (by omega)
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] at heN
      have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hb := (div_lt_iff₀ hNr).mp heN
      linarith

/-- Natural Cesàro cancellation implies ordinary exponential cancellation. -/
theorem exponential_zero_of_cesaro_zero (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ range N, f n)/N) atTop (𝓝 0)) :
    Tendsto (exponentialMean f) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨C,hC,hbound⟩ := exists_affine_prefix_bound f hmean (δ/3) (by positivity)
  have ht : Tendsto (fun t : ℝ => C*t+(δ/3)*(1+t)) (𝓝[>] 0) (𝓝 (δ/3)) := by
    have hc : ContinuousAt (fun t : ℝ => C*t+(δ/3)*(1+t)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, ht.eventually_lt_const (by linarith : δ/3 < δ)] with t htpos htδ
  rw [Real.dist_eq, sub_zero]
  exact (exponential_mean_affine_bound f hf (by positivity) htpos hbound).trans_lt htδ

/-- For bounded sequences, ordinary exponential and natural cancellation
are equivalent. No logarithmic or Dirichlet-Abel hypothesis occurs here. -/
theorem exponential_zero_iff_cesaro_zero (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) :
    Tendsto (exponentialMean f) (𝓝[>] 0) (𝓝 0) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ range N, f n)/N) atTop (𝓝 0) :=
  ⟨cesaro_zero_of_exponential_zero f hf, exponential_zero_of_cesaro_zero f hf⟩

/-- A uniform signed prefix bound controls exponential smoothing with
no bound on the individual terms supplied as an extra hypothesis. -/
theorem exponential_mean_of_bounded_prefix (f : ℕ → ℝ) {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t) (hprefix : ∀ N : ℕ, |partialSum f N| ≤ C) :
    |exponentialMean f t| ≤ C*t := by
  let a : ℝ := 2*C+1
  have ha : 0 < a := by dsimp [a]; linarith
  let g : ℕ → ℝ := fun n => f n/a
  have hg : ∀ n, |g n| ≤ 1 := by
    intro n
    have he : f n = partialSum f (n+1)-partialSum f n := by
      simp [partialSum, sum_range_succ]
    have hb : |f n| ≤ 2*C := by
      rw [he]
      exact (abs_sub _ _).trans (by linarith [hprefix (n+1), hprefix n])
    dsimp only [g]
    rw [abs_div, abs_of_pos ha, div_le_one ha]
    dsimp [a]
    linarith
  have hgp (N : ℕ) : |partialSum g N| ≤ C/a+0*N := by
    simp only [partialSum, g, ← sum_div, abs_div, abs_of_pos ha, zero_mul, add_zero]
    exact div_le_div_of_nonneg_right (hprefix N) ha.le
  have hb := exponential_mean_affine_bound g hg (by norm_num : (0 : ℝ) ≤ 0) ht hgp
  have he : exponentialMean g t = exponentialMean f t/a := by
    simp only [exponentialMean, g]
    have hh (n : ℕ) : f n/a*Real.exp (-t*n) = (f n*Real.exp (-t*n))/a := by ring
    simp only [hh]
    rw [tsum_div_const, mul_div_assoc]
  rw [he, abs_div, abs_of_pos ha, zero_mul, add_zero] at hb
  have h := (div_le_iff₀ ha).mp hb
  convert h using 1
  field_simp

#print axioms exponential_mean_of_bounded_prefix

#print axioms exponential_mean_affine_bound
#print axioms exponential_zero_iff_cesaro_zero
end Erdos371.ExponentialWindow
