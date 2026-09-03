import Submission.NaturalAutocorrelationExplore
import Submission.AbelErrorEnergyExplore

/-! An Abel ratio lemma and a logarithmic-square bound for the harmonic
normalizer, for the natural autocorrelation necessary condition. -/
namespace Erdos66AutocorrelationAbel
open Erdos66Generating Erdos66ResidueSeries Erdos66AbelErrorEnergy
  Erdos66Fractional Filter
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma ratio_zero_abel {u v : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hv1 : ∀ n, 1 ≤ v n)
    (hu : ∀ r : ℝ, 0<r → r<1 → Summable (fun n ↦ u n*r^n))
    (hv : ∀ r : ℝ, 0<r → r<1 → Summable (fun n ↦ v n*r^n))
    (h : Tendsto (fun n ↦ u n/v n) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ ↦ series u r/series v r) (𝓝[<] 1) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h.eventually_lt_const (by linarith : (0:ℝ)<ε/2))
  let D := ∑ n∈Finset.range N, u n
  have hD : 0 ≤ D := Finset.sum_nonneg (fun n _ ↦ hu0 n)
  have ht : Tendsto (fun r : ℝ ↦ D*(1-r)) (𝓝[<] 1) (𝓝 0) := by
    have hh : Tendsto (fun r : ℝ ↦ r) (𝓝[<] 1) (𝓝 1) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa using (hh.const_sub 1).const_mul D
  filter_upwards [unit_interval_eventually,ht.eventually_lt_const (by linarith : (0:ℝ)<ε/2)]
    with r hr hsmall
  have hgeom := summable_geometric_of_lt_one hr.1.le hr.2
  have hVlow : (1-r)⁻¹ ≤ series v r := by
    rw [← tsum_geometric_of_lt_one hr.1.le hr.2]
    exact hgeom.tsum_le_tsum (fun n ↦ by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hv1 n) (pow_nonneg hr.1.le n))
      (hv r hr.1 hr.2)
  have hVpos : 0<series v r := (inv_pos.mpr (sub_pos.mpr hr.2)).trans_le hVlow
  have hU0 : 0 ≤ series u r := tsum_nonneg (fun n ↦ mul_nonneg (hu0 n) (pow_nonneg hr.1.le n))
  let d : ℕ → ℝ := fun n ↦ if n∈Finset.range N then u n*r^n else 0
  have hd : Summable d := summable_of_ne_finset_zero (s := Finset.range N)
    (fun n hn ↦ by simp only [d,if_neg hn])
  have hdD : (∑' n, d n) ≤ D := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn ↦ by simp only [d,if_neg hn])]
    apply Finset.sum_le_sum
    intro n hn
    dsimp [d]
    rw [if_pos hn]
    exact mul_le_of_le_one_right (hu0 n) (pow_le_one₀ hr.1.le hr.2.le)
  have hpoint (n : ℕ) : u n*r^n ≤ (ε/2)*(v n*r^n)+d n := by
    by_cases hn : n<N
    · have hh : 0 ≤ (ε/2)*(v n*r^n) := mul_nonneg (by linarith)
        (mul_nonneg (by have := hv1 n; linarith) (pow_nonneg hr.1.le n))
      simp only [d,Finset.mem_range,if_pos hn]
      linarith
    · have hvn : 0<v n := lt_of_lt_of_le zero_lt_one (hv1 n)
      have hh := ((div_lt_iff₀ hvn).mp (hN n (by omega))).le
      have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg hr.1.le n)
      simpa only [d,Finset.mem_range,if_neg hn,add_zero,mul_assoc] using hm
  have hsum := (hu r hr.1 hr.2).tsum_le_tsum hpoint (((hv r hr.1 hr.2).mul_left (ε/2)).add hd)
  rw [Summable.tsum_add ((hv r hr.1 hr.2).mul_left (ε/2)) hd,tsum_mul_left] at hsum
  change series u r ≤ (ε/2)*series v r+(∑' n, d n) at hsum
  have hmain : series u r ≤ (ε/2)*series v r+D := hsum.trans (by linarith)
  have hDV : D/series v r ≤ D*(1-r) := by
    have hh := div_le_div_of_nonneg_left hD (inv_pos.mpr (sub_pos.mpr hr.2)) hVlow
    simpa only [div_inv_eq_mul] using hh
  have hratio : series u r/series v r < ε := by
    have hh := (div_le_div_of_nonneg_right hmain hVpos.le)
    rw [add_div,mul_div_cancel_right₀ _ hVpos.ne'] at hh
    linarith
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg hU0 hVpos.le)] using hratio

lemma harmonic_succ_ge_one (n : ℕ) : 1 ≤ (harmonic (n+1) : ℝ) := by
  induction n with
  | zero => norm_num [harmonic]
  | succ n ih =>
    rw [harmonic_succ]
    push_cast
    have hn : 0 ≤ (((n:ℝ)+1)+1)⁻¹ := by positivity
    linarith

lemma summable_harmonic_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r<1) :
    Summable (fun n ↦ (harmonic (n+1) : ℝ)^2*r^n) := by
  have hnr : ‖r‖<1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hr0] using hr1
  have hs := (summable_pow_mul_geometric_of_norm_lt_one 2 hnr).add
    (((summable_pow_mul_geometric_of_norm_lt_one 1 hnr).mul_left 2).add
      (summable_geometric_of_lt_one hr0 hr1))
  apply hs.of_norm_bounded
  intro n
  have hh : (harmonic (n+1) : ℝ)≤(n:ℝ)+1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using harmonic_le_nat (n+1)
  have hh2 := (sq_le_sq₀ (harmonic_nonneg (n+1)) (by positivity)).mpr hh
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((n:ℝ)+1)^2*r^n := mul_le_mul_of_nonneg_right hh2 (pow_nonneg hr0 n)
    _ = _ := by ring

noncomputable def harmonicSqSeries (r : ℝ) : ℝ :=
  series (fun n ↦ (harmonic (n+1) : ℝ)^2) r

/-- A bound uniform in the radius. The constant is not claimed optimal. -/
lemma harmonic_sq_series_bound {r : ℝ} (hr0 : 0<r) (hr1 : r<1)
    (hL : 1 ≤ -Real.log (1-r)) :
    harmonicSqSeries r ≤ 6*(-Real.log (1-r))^2/(1-r) := by
  let L := -Real.log (1-r)
  have ht : 0<1-r := sub_pos.mpr hr1
  have hnr : ‖r‖<1 := by simpa only [Real.norm_eq_abs,abs_of_pos hr0] using hr1
  have hH (n : ℕ) : (harmonic (n+1) : ℝ) ≤ L+(1-r)*((n:ℝ)+1) := by
    have hl := Real.log_le_sub_one_of_pos (mul_pos ht (by positivity : (0:ℝ)<(n:ℝ)+1))
    rw [Real.log_mul ht.ne' (by positivity)] at hl
    have hh := harmonic_le_one_add_log (n+1)
    simp only [Nat.cast_add,Nat.cast_one] at hh
    dsimp [L]
    linarith
  have hb (n : ℕ) : (harmonic (n+1) : ℝ)^2 ≤
      2*L^2+4*(1-r)^2*((n+2).choose 2 : ℝ) := by
    have hs := (sq_le_sq₀ (harmonic_nonneg (n+1)) (by dsimp [L]; positivity)).mpr (hH n)
    have hbin : ((n:ℝ)+1)^2 ≤ 2*((n+2).choose 2 : ℝ) := by
      rw [Nat.cast_choose_two]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith [sq_nonneg (L-(1-r)*((n:ℝ)+1)),
      mul_le_mul_of_nonneg_left hbin (sq_nonneg (1-r))]
  have hc := summable_choose_mul_geometric_of_norm_lt_one 2 hnr
  have hg := summable_geometric_of_lt_one hr0.le hr1
  have hu := (hg.mul_left (2*L^2)).add (hc.mul_left (4*(1-r)^2))
  have hh := (summable_harmonic_sq hr0.le hr1).tsum_le_tsum
    (fun n ↦ (mul_le_mul_of_nonneg_right (hb n) (pow_nonneg hr0.le n)).trans_eq (by ring)) hu
  rw [Summable.tsum_add (hg.mul_left (2*L^2)) (hc.mul_left (4*(1-r)^2)),
    tsum_mul_left,tsum_mul_left,tsum_geometric_of_lt_one hr0.le hr1,
    tsum_choose_mul_geometric_of_norm_lt_one 2 hnr] at hh
  change harmonicSqSeries r ≤ _ at hh
  calc
    harmonicSqSeries r ≤ 2*L^2*(1-r)⁻¹+4*(1-r)^2*(1/(1-r)^3) := hh
    _ = (2*L^2+4)/(1-r) := by field_simp
    _ ≤ 6*L^2/(1-r) := by
      apply div_le_div_of_nonneg_right _ ht.le
      change 1 ≤ L at hL
      nlinarith

/-- The witness hypothesis makes the squared representation error negligible
relative to the harmonic-square Abel normalizer. -/
theorem witness_error_ratio_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (AdditiveCombinatorics.sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ ↦ series (errorSq A c) r/harmonicSqSeries r) (𝓝[<] 1) (𝓝 0) := by
  apply ratio_zero_abel (fun n ↦ sq_nonneg _)
    (fun n ↦ by have := harmonic_succ_ge_one n; nlinarith)
    (fun _ hr0 hr1 ↦ summable_errorSq A c hr0.le hr1)
    (fun _ hr0 hr1 ↦ summable_harmonic_sq hr0.le hr1)
  have hh := (h.div harmonic_shift_log_ratio (by norm_num : (1:ℝ)≠0)).sub_const c
  simp only [div_one,sub_self] at hh
  have hs := hh.pow 2
  simp only [zero_pow (by decide : 2≠0)] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hl : Real.log (n:ℝ)≠0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  dsimp [errorSq]
  rw [div_div_div_cancel_right₀ hl]
  rw [← div_pow,sub_div,mul_div_cancel_right₀ _ (by
    have := harmonic_succ_ge_one n; linarith : (harmonic (n+1) : ℝ)≠0)]

end Erdos66AutocorrelationAbel
