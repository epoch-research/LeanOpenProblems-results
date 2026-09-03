import Submission.TauberianGeneralExplore

/-! Ordinary (not only geometrically weighted) residue equidistribution of
every hypothetical witness to Erdős Problem 66. -/
namespace Erdos66ResidueCounting
open Filter AdditiveCombinatorics Erdos66Generating Erdos66TauberianGeneral
  Erdos66TauberianProfile Erdos66Counting Erdos66ResidueEquidistribution Erdos66ResidueSeries
open scoped Topology Classical

variable (m : ℕ) [NeZero m]

def residueSet (A : Set ℕ) (z : ZMod m) : Set ℕ := {n | n ∈ A ∧ (n : ZMod m) = z}

omit [NeZero m] in
lemma series_residueSet (A : Set ℕ) (z : ZMod m) (r : ℝ) :
    series (indicator (residueSet m A z)) r = residueMass m A r z := by
  unfold series residueMass push
  apply tsum_congr
  intro n
  by_cases ha : n ∈ A <;> by_cases hz : (n : ZMod m) = z <;>
    simp [residueSet, indicator, residueTerm, weightedIndicator, ha, hz]

lemma residue_generating_profile {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) (z : ZMod m) :
    Tendsto (fun r : ℝ ↦ series (indicator (residueSet m A z)) r * Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 (Real.sqrt c / m)) := by
  have hR := witness_residue_equidistribution m hc h z
  have hG : Tendsto (fun r : ℝ ↦ series (indicator A) r * Real.sqrt (kernel r))
      (𝓝[<] 1) (𝓝 (Real.sqrt c)) := witness_generating_limit h
  have hh := hR.mul hG
  have he : (1 / (m : ℝ)) * Real.sqrt c = Real.sqrt c / m := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [witness_series_eventually_ne_zero hc h] with r hF
  rw [series_residueSet]
  dsimp only [normalizedMass]
  field_simp

/-- The ordinary counting function in each fixed residue class has exactly
`1/m` of the full main term. -/
theorem witness_residue_counting_profile {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) (z : ZMod m) :
    Tendsto (fun N ↦ (count (residueSet m A z) N : ℝ) /
      Real.sqrt ((N : ℝ) * Real.log N)) atTop
      (𝓝 ((2 * Real.sqrt c / Real.sqrt Real.pi) / m)) := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hd : Real.sqrt c / m ≠ 0 := div_ne_zero (Real.sqrt_ne_zero'.mpr hcpos) hm
  have hh := counting_profile_of_generating_profile hd (residue_generating_profile m hc h z)
  have he : 2 * (Real.sqrt c / (m : ℝ)) / Real.sqrt Real.pi =
      (2 * Real.sqrt c / Real.sqrt Real.pi) / m := by ring
  rwa [he] at hh

/-- Every fixed residue class contains asymptotically `1/m` of the actual
prefix of a hypothetical witness, not merely of its Abel-weighted mass. -/
theorem witness_ordinary_residue_equidistribution {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) (z : ZMod m) :
    Tendsto (fun N ↦ (count (residueSet m A z) N : ℝ) / count A N) atTop (𝓝 (1 / m)) := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hd : Real.sqrt c ≠ 0 := Real.sqrt_ne_zero'.mpr hcpos
  have hC := counting_profile_of_generating_profile hd (witness_generating_limit h)
  have hR := witness_residue_counting_profile m hc h z
  have hC0 : 2 * Real.sqrt c / Real.sqrt Real.pi ≠ 0 := by positivity
  have hh := hR.div hC hC0
  have he : ((2 * Real.sqrt c / Real.sqrt Real.pi) / m) /
      (2 * Real.sqrt c / Real.sqrt Real.pi) = 1 / m := by field_simp
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hden : Real.sqrt ((N : ℝ) * Real.log N) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos (by linarith) (Real.log_pos hn))
  exact div_div_div_cancel_right₀ hden _ _

end Erdos66ResidueCounting
