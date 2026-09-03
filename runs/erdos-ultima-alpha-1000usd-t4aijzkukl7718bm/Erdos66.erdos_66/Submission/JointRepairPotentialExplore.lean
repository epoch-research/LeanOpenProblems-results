import Submission.ClippedRepairExplore

/-! Summable exponential potentials for mixed hits of a jointly selected sparse
family. Thresholds can be fixed before the number of selected coordinates. -/
namespace Erdos66JointRepairPotential
open Filter Erdos66ClippedRepair
open scoped Topology Classical
set_option maxHeartbeats 1000000

noncomputable def potential (B ε : ℝ) (z : ℕ) : ℝ :=
  Real.exp (Real.exp (4 / ε) * B * Real.sqrt (logScale z) - 4 * logScale z)

lemma potential_pos (B ε : ℝ) (z : ℕ) : 0 < potential B ε z := Real.exp_pos _

lemma sqrt_logScale_div_limit :
    Tendsto (fun z : ℕ ↦ Real.sqrt (logScale z) / logScale z) atTop (𝓝 0) := by
  simp only [Real.sqrt_div_self]
  exact (Real.tendsto_sqrt_atTop.comp logScale_atTop).inv_tendsto_atTop

lemma eventually_potential_le (B ε : ℝ) :
    ∀ᶠ z : ℕ in atTop, potential B ε z ≤ 1 / ((z : ℝ)+2)^2 := by
  have hh := sqrt_logScale_div_limit.const_mul (Real.exp (4 / ε) * B)
  simp only [mul_zero] at hh
  filter_upwards [hh.eventually_lt_const (show (0 : ℝ) < 2 by norm_num)] with z hz
  have hbound : Real.exp (4 / ε) * B * Real.sqrt (logScale z) ≤ 2 * logScale z := by
    have he := (div_lt_iff₀ (logScale_pos z)).mp
      (show (Real.exp (4 / ε) * B * Real.sqrt (logScale z)) / logScale z < 2 by
        simpa only [mul_div_assoc] using hz)
    exact he.le
  calc
    potential B ε z ≤ Real.exp (-(2 * logScale z)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = 1 / ((z : ℝ)+2)^2 := by
      rw [Real.exp_neg]
      have he : Real.exp (2 * logScale z) = ((z : ℝ)+2)^2 := by
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.exp_nat_mul]
        rw [logScale, Real.exp_log (by positivity)]
        norm_num
      rw [he, one_div]

lemma potential_summable (B ε : ℝ) : Summable (potential B ε) := by
  have hp : Summable (fun z : ℕ ↦ 1 / ((z : ℝ)+2)^2) := by
    have hh : Summable (fun z : ℕ ↦ 1 / (z : ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_ofNat] using (summable_nat_add_iff 2).mpr hh
  apply hp.of_norm_bounded_eventually_nat
  filter_upwards [eventually_potential_le B ε] with z hz
  simpa only [Real.norm_eq_abs, abs_of_pos (potential_pos B ε z)] using hz

/-- Every finite test set beyond one threshold has arbitrarily small total
potential. The threshold does not depend on the finite test set. -/
theorem exists_uniform_tail_threshold (B ε δ : ℝ) (hδ : 0 < δ) :
    ∃ Z : ℕ, ∀ T : Finset ℕ, (∀ z ∈ T, Z ≤ z) →
      ∑ z ∈ T, potential B ε z < δ := by
  obtain ⟨Z, hZ⟩ := ((tendsto_sum_nat_add (potential B ε)).eventually_lt_const hδ).exists
  refine ⟨Z, fun T hT ↦ ?_⟩
  let U := T.image (fun z ↦ z-Z)
  have hinj : Set.InjOn (fun z ↦ z-Z) (T : Set ℕ) := by
    intro a ha b hb he
    have ha' := hT a ha
    have hb' := hT b hb
    dsimp only at he
    omega
  have he : (∑ z ∈ T, potential B ε z) = ∑ u ∈ U, potential B ε (u+Z) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro z hz
      rw [Nat.sub_add_cancel (hT z hz)]
    · exact hinj
  rw [he]
  have hs := (summable_nat_add_iff Z).mpr (potential_summable B ε)
  exact (hs.sum_le_tsum U (fun u _ ↦ (potential_pos B ε (u+Z)).le)).trans_lt hZ

lemma hit_potential_le (B ε H : ℝ) (hε : 0 < ε) (z : ℕ)
    (hH : H ≤ B * Real.sqrt (logScale z)) :
    Real.exp (Real.exp (4 / ε) * H - (4 / ε) * (ε * logScale z)) ≤ potential B ε z := by
  have he : (4 / ε) * (ε * logScale z) = 4 * logScale z := by field_simp
  rw [he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hH (Real.exp_pos (4 / ε)).le
  nlinarith

/-- A countable family of accuracy levels may each receive a fixed tail
threshold and a summable share of the joint potential budget. -/
theorem exists_accuracy_thresholds (B : ℝ) (ε δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ Z : ℕ → ℕ, ∀ k (T : Finset ℕ), (∀ z ∈ T, Z k ≤ z) →
      ∑ z ∈ T, potential B (ε k) z < δ k := by
  choose Z hZ using fun k ↦ exists_uniform_tail_threshold B (ε k) (δ k) (hδ k)
  exact ⟨Z,hZ⟩

end Erdos66JointRepairPotential
