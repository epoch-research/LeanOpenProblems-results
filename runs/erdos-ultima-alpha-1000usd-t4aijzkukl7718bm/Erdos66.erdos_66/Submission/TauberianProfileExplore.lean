import Submission.TauberianCutoffExplore

/-! The exact counting profile forced by a nonzero logarithmic representation
limit. This is a necessary condition and is not a construction of a witness. -/
namespace Erdos66TauberianProfile
open Filter MeasureTheory AdditiveCombinatorics Erdos66Generating Erdos66TauberianTests
  Erdos66TauberianCutoff Erdos66Counting
open scoped Topology

noncomputable def radius (N : ℕ) : ℝ := 1 - 1 / (N : ℝ)

lemma radius_bounds {N : ℕ} (hN : 2 ≤ N) : 0 < radius N ∧ radius N < 1 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpos : 0 < (N : ℝ) := by linarith
  have hh : 1 / (N : ℝ) < 1 := (div_lt_one hpos).mpr hNr
  dsimp [radius]
  constructor
  · linarith
  · exact sub_lt_self _ (one_div_pos.mpr hpos)

lemma radius_tendsto : Tendsto radius atTop (𝓝[<] 1) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hh := (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop 1
    simpa only [sub_zero, radius] using hh.const_sub 1
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact (radius_bounds hN).2

lemma radius_pow_tendsto : Tendsto (fun N ↦ radius N ^ N) atTop (𝓝 (Real.exp (-1))) := by
  simpa only [radius, neg_div, one_div, sub_eq_add_neg] using Real.tendsto_one_add_div_pow_exp (-1)

/-- A Tauberian transfer from the weighted moments to the prefix count,
normalized by the generating function at `1-1/N`. -/
lemma count_series_ratio_limit_of_tests {A : Set ℕ}
    (hTests : ∀ g : C(I, ℝ), Tendsto (fun r ↦ test A r g) (𝓝[<] 1) (𝓝 (gaussTest g))) :
    Tendsto (fun N ↦ (count A N : ℝ) / series (indicator A) (radius N)) atTop
      (𝓝 (2 / Real.sqrt Real.pi)) := by
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  apply tendsto_order.mpr
  constructor
  · intro z hz
    have hz' : z * Real.sqrt Real.pi / 2 < 1 := by
      have hh := (lt_div_iff₀ hpi).mp hz
      linarith
    obtain ⟨u, hu, hu1⟩ := exists_between (show max 0 (z * Real.sqrt Real.pi / 2) < 1 by
      exact max_lt (by norm_num) hz')
    have hu0 : 0 < u := (le_max_left _ _).trans_lt hu
    have hzu : z < 2 * u / Real.sqrt Real.pi := by
      apply (lt_div_iff₀ hpi).mpr
      have hh := (le_max_right _ _).trans_lt hu
      linarith
    let v := (u + 1) / 2
    have huv : u < v := by dsimp [v]; linarith
    have hv1 : v < 1 := by dsimp [v]; linarith
    have hv0 : 0 < v := hu0.trans huv
    let g := window (Real.exp (-v ^ 2)) (Real.exp (-u ^ 2)) (Real.exp_pos _)
    have hgz : z < gaussTest g :=
      hzu.trans_le (gaussTest_window_bounds hu0.le huv).1
    have htest := ((hTests g).comp radius_tendsto).eventually (eventually_gt_nhds hgz)
    have hpow : ∀ᶠ N in atTop, radius N ^ N < Real.exp (-v ^ 2) :=
      radius_pow_tendsto.eventually_lt_const (Real.exp_lt_exp.mpr (by nlinarith))
    filter_upwards [eventually_ge_atTop 2, htest, hpow] with N hN ht hp
    exact ht.trans_le (test_window_le_count A (radius_bounds hN).1.le (radius_bounds hN).2.le
      (Real.exp_pos _) (exp_cutoff_order hu0.le huv) hp.le)
  · intro z hz
    have hz' : 1 < z * Real.sqrt Real.pi / 2 := by
      have hh := (div_lt_iff₀ hpi).mp hz
      linarith
    obtain ⟨v, hv1, hvz⟩ := exists_between hz'
    let u := (1 + v) / 2
    have hu1 : 1 < u := by dsimp [u]; linarith
    have huv : u < v := by dsimp [u]; linarith
    have hu0 : 0 < u := by linarith
    have hvz' : 2 * v / Real.sqrt Real.pi < z := by
      apply (div_lt_iff₀ hpi).mpr
      linarith
    let g := window (Real.exp (-v ^ 2)) (Real.exp (-u ^ 2)) (Real.exp_pos _)
    have hgz : gaussTest g < z :=
      (gaussTest_window_bounds hu0.le huv).2.trans_lt hvz'
    have htest := ((hTests g).comp radius_tendsto).eventually_lt_const hgz
    have hpow : ∀ᶠ N in atTop, Real.exp (-u ^ 2) < radius N ^ N :=
      radius_pow_tendsto.eventually (eventually_gt_nhds (Real.exp_lt_exp.mpr (by nlinarith)))
    filter_upwards [eventually_ge_atTop 2, htest, hpow] with N hN ht hp
    exact (count_le_test_window A (radius_bounds hN).1.le (radius_bounds hN).2
      (Real.exp_pos _) (exp_cutoff_order hu0.le huv) hp.le).trans_lt ht

lemma series_radius_limit_of_generating_limit {A : Set ℕ} {d : ℝ}
    (h : Tendsto (fun r : ℝ ↦ series (indicator A) r *
      Real.sqrt ((1 - r) / (-Real.log (1 - r)))) (𝓝[<] 1) (𝓝 d)) :
    Tendsto (fun N ↦ series (indicator A) (radius N) /
      Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 d) := by
  have hh := h.comp radius_tendsto
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hNr)
  have he : 1 - radius N = (N : ℝ)⁻¹ := by dsimp [radius]; ring
  change series (indicator A) (radius N) * Real.sqrt ((1 - radius N) /
    (-Real.log (1 - radius N))) = _
  rw [he, Real.log_inv, neg_neg]
  have hi : (N : ℝ)⁻¹ / Real.log N = ((N : ℝ) * Real.log N)⁻¹ := by field_simp
  rw [hi, Real.sqrt_inv, div_eq_mul_inv]

lemma count_series_ratio_limit {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count A N : ℝ) / series (indicator A) (radius N)) atTop
      (𝓝 (2 / Real.sqrt Real.pi)) :=
  count_series_ratio_limit_of_tests (continuous_test_limit hc h)

lemma series_radius_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ series (indicator A) (radius N) /
      Real.sqrt ((N : ℝ) * Real.log N)) atTop (𝓝 (Real.sqrt c)) :=
  series_radius_limit_of_generating_limit (witness_generating_limit h)

/-- Exact ordinary counting asymptotic of every hypothetical witness. -/
theorem witness_counting_profile {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count A N : ℝ) / Real.sqrt ((N : ℝ) * Real.log N)) atTop
      (𝓝 (2 * Real.sqrt (c / Real.pi))) := by
  have hh := (count_series_ratio_limit hc h).mul (series_radius_limit h)
  have hcpos := Erdos66Explore.limit_pos hc h
  have he : (2 / Real.sqrt Real.pi) * Real.sqrt c = 2 * Real.sqrt (c / Real.pi) := by
    rw [Real.sqrt_div hcpos.le]
    ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [radius_tendsto.eventually
    (Erdos66ResidueEquidistribution.witness_series_eventually_ne_zero hc h)] with N hF
  field_simp

/-- The normalized square of the counting function tends to `4c/π`,
strictly larger than the representation coefficient. -/
theorem witness_counting_square_profile {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count A N : ℝ) ^ 2 / ((N : ℝ) * Real.log N)) atTop
      (𝓝 (4 * c / Real.pi)) := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hh := (witness_counting_profile hc h).pow 2
  have he : (2 * Real.sqrt (c / Real.pi)) ^ 2 = 4 * c / Real.pi := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hcpos.le Real.pi_pos.le)]
    ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [div_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))]

end Erdos66TauberianProfile
