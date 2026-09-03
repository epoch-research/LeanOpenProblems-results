import Submission.TauberianTestsExplore

/-! Continuous cutoffs for recovering ordinary prefix counts from the
Laplace-weighted continuous test limits. -/
namespace Erdos66TauberianCutoff
open Filter MeasureTheory AdditiveCombinatorics Erdos66Generating Erdos66TauberianTests
  Erdos66Counting
open scoped Topology Classical

noncomputable def ramp (a b x : ℝ) : ℝ := max 0 (min 1 ((x - a) / (b - a)))

lemma ramp_nonneg (a b x : ℝ) : 0 ≤ ramp a b x := le_max_left _ _
lemma ramp_le_one (a b x : ℝ) : ramp a b x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma ramp_zero {a b x : ℝ} (hab : a < b) (hx : x ≤ a) : ramp a b x = 0 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_nonneg.mpr hab.le))

lemma ramp_one {a b x : ℝ} (hab : a < b) (hx : b ≤ x) : ramp a b x = 1 := by
  have hh : 1 ≤ (x - a) / (b - a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  simp only [ramp, min_eq_left hh, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

@[fun_prop] lemma continuous_ramp (a b : ℝ) : Continuous (ramp a b) := by unfold ramp; fun_prop

noncomputable def window (a b : ℝ) (ha : 0 < a) : C(I, ℝ) where
  toFun x := ramp a b x / max (x : ℝ) a
  continuous_toFun := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact ne_of_gt (lt_of_lt_of_le ha (le_max_right _ _))

lemma window_mul {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : I) :
    (x : ℝ) * window a b ha x = ramp a b x := by
  change (x : ℝ) * (ramp a b x / max (x : ℝ) a) = _
  by_cases hx : a ≤ (x : ℝ)
  · rw [max_eq_left hx]
    have hx0 : (x : ℝ) ≠ 0 := ne_of_gt (ha.trans_le hx)
    field_simp
  · rw [ramp_zero hab (le_of_not_ge hx)]
    ring

lemma window_nonneg {a b : ℝ} (ha : 0 < a) (x : I) : 0 ≤ window a b ha x :=
  div_nonneg (ramp_nonneg _ _ _) (ha.le.trans (le_max_right _ _))

lemma exp_cutoff_order {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Real.exp (-v ^ 2) < Real.exp (-u ^ 2) := by
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- The limiting test functional of a window between `exp(-v²)` and
`exp(-u²)` lies between the two corresponding interval lengths. -/
lemma gaussTest_window_bounds {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    2 * u / Real.sqrt Real.pi ≤
      gaussTest (window (Real.exp (-v ^ 2)) (Real.exp (-u ^ 2)) (Real.exp_pos _)) ∧
    gaussTest (window (Real.exp (-v ^ 2)) (Real.exp (-u ^ 2)) (Real.exp_pos _)) ≤
      2 * v / Real.sqrt Real.pi := by
  let a := Real.exp (-v ^ 2)
  let b := Real.exp (-u ^ 2)
  have ha : 0 < a := Real.exp_pos _
  have hab : a < b := exp_cutoff_order hu huv
  let g := window a b ha
  have he (x : ℝ) : Real.exp (-x ^ 2) * g (gaussPoint x) = ramp a b (Real.exp (-x ^ 2)) :=
    window_mul ha hab (gaussPoint x)
  have hlow (x : ℝ) : (Set.Icc (-u) u).indicator (fun _ : ℝ ↦ (1 : ℝ)) x ≤
      Real.exp (-x ^ 2) * g (gaussPoint x) := by
    rw [he]
    by_cases hx : x ∈ Set.Icc (-u) u
    · rw [Set.indicator_of_mem hx]
      have hsq : x ^ 2 ≤ u ^ 2 := by
        have hh := mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ x + u by linarith [hx.1])
        nlinarith
      rw [ramp_one hab (Real.exp_le_exp.mpr (by linarith))]
    · rw [Set.indicator_of_notMem hx]
      exact ramp_nonneg _ _ _
  have hupp (x : ℝ) : Real.exp (-x ^ 2) * g (gaussPoint x) ≤
      (Set.Icc (-v) v).indicator (fun _ : ℝ ↦ (1 : ℝ)) x := by
    rw [he]
    by_cases hx : x ∈ Set.Icc (-v) v
    · rw [Set.indicator_of_mem hx]
      exact ramp_le_one _ _ _
    · rw [Set.indicator_of_notMem hx]
      have hsq : v ^ 2 ≤ x ^ 2 := by
        have hv : 0 < v := hu.trans_lt huv
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx <;> nlinarith
      rw [ramp_zero hab (Real.exp_le_exp.mpr (by linarith))]
  have hIu : Integrable ((Set.Icc (-u) u).indicator (fun _ : ℝ ↦ (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hIv : Integrable ((Set.Icc (-v) v).indicator (fun _ : ℝ ↦ (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have h₁ := integral_mono hIu (integrable_gauss_test g) hlow
  have h₂ := integral_mono (integrable_gauss_test g) hIv hupp
  have hpi := (Real.sqrt_pos.mpr Real.pi_pos).le
  have hu' : 0 ≤ u - -u := by linarith
  have hv' : 0 ≤ v - -v := by linarith
  simp only [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Icc, max_eq_left hu', max_eq_left hv'] at h₁ h₂
  constructor
  · change 2 * u / Real.sqrt Real.pi ≤ gaussTest g
    dsimp only [gaussTest]
    exact div_le_div_of_nonneg_right (by linarith) hpi
  · change gaussTest g ≤ 2 * v / Real.sqrt Real.pi
    dsimp only [gaussTest]
    exact div_le_div_of_nonneg_right (by linarith) hpi

lemma sum_indicator_eq_count (A : Set ℕ) (N : ℕ) :
    (∑ n ∈ Finset.range N, indicator A n) = (count A N : ℝ) := by
  unfold count cutoff
  rw [Finset.card_filter]
  push_cast
  rfl

lemma test_window_formula (A : Set ℕ) {r a b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : 0 < a) (hab : a < b) :
    test A r (window a b ha) = (∑' n, indicator A n * ramp a b (r ^ n)) /
      series (indicator A) r := by
  unfold test
  congr 1
  apply tsum_congr
  intro n
  have hn : r ^ n ∈ I := ⟨pow_nonneg hr0 n, pow_le_one₀ hr0 hr1⟩
  have hh := window_mul ha hab (clip (r ^ n))
  rw [clip_coe hn] at hh
  rw [mul_assoc, hh]

lemma summable_ramp (A : Set ℕ) {r a b : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : 0 < a) (hab : a < b) : Summable (fun n ↦ indicator A n * ramp a b (r ^ n)) := by
  have hh := summable_test A (by rwa [abs_of_nonneg hr0]) (window a b ha)
  convert hh using 1
  funext n
  have hn : r ^ n ∈ I := ⟨pow_nonneg hr0 n, pow_le_one₀ hr0 hr1.le⟩
  have he := window_mul ha hab (clip (r ^ n))
  rw [clip_coe hn] at he
  rw [mul_assoc, he]

lemma test_window_le_count (A : Set ℕ) {N : ℕ} {r a b : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 < a) (hab : a < b) (hNa : r ^ N ≤ a) :
    test A r (window a b ha) ≤ (count A N : ℝ) / series (indicator A) r := by
  rw [test_window_formula A hr0 hr1 ha hab]
  have hz (n : ℕ) (hn : n ∉ Finset.range N) : indicator A n * ramp a b (r ^ n) = 0 := by
    have hNn : N ≤ n := by simpa using hn
    have hpow : r ^ n ≤ r ^ N := pow_le_pow_of_le_one hr0 hr1 hNn
    rw [ramp_zero hab (hpow.trans hNa), mul_zero]
  rw [tsum_eq_sum hz]
  apply div_le_div_of_nonneg_right _ (Erdos66Generating.series_indicator_nonneg A hr0)
  rw [← sum_indicator_eq_count]
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_of_le_one_right (indicator_nonneg A n) (ramp_le_one _ _ _)

lemma count_le_test_window (A : Set ℕ) {N : ℕ} {r a b : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : 0 < a) (hab : a < b) (hbN : b ≤ r ^ N) :
    (count A N : ℝ) / series (indicator A) r ≤ test A r (window a b ha) := by
  rw [test_window_formula A hr0 hr1.le ha hab]
  apply div_le_div_of_nonneg_right _ (Erdos66Generating.series_indicator_nonneg A hr0)
  have he : (count A N : ℝ) = ∑ n ∈ Finset.range N, indicator A n * ramp a b (r ^ n) := by
    rw [← sum_indicator_eq_count]
    apply Finset.sum_congr rfl
    intro n hn
    have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
    have hpow : r ^ N ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1.le hnN
    rw [ramp_one hab (hbN.trans hpow), mul_one]
  rw [he]
  exact (summable_ramp A hr0 hr1 ha hab).sum_le_tsum _
    (fun n _ ↦ mul_nonneg (indicator_nonneg A n) (ramp_nonneg _ _ _))

end Erdos66TauberianCutoff
