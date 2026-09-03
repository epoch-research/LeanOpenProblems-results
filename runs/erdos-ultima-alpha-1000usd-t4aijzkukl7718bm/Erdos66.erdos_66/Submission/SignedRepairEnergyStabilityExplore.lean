import Submission.SignedRepairEnergyExplore

/-! Limiting lower bounds for the aggregate incidence energy of a signed
repair. These are necessary conditions, with no assertion that the energy
is small for an actual exceptional set. -/
namespace Erdos66SignedRepairEnergyStability
open Erdos66SignedRepairEnergy Erdos66SignedRepairIncidence
  Erdos66UnrestrictedRepairIncidence Erdos66Counting
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 2400000

lemma cardinal_center_tendsto (A B : ℕ → Finset ℕ) (R : ℕ → ℝ) (a β : ℝ)
    (hA : Tendsto (fun k ↦ ((A k).card : ℝ)/R k) atTop (𝓝 a))
    (hB : Tendsto (fun k ↦ ((B k).card : ℝ)/R k) atTop (𝓝 a)) :
    Tendsto (fun k ↦ β*((B k).card-(A k).card)/R k) atTop (𝓝 0) := by
  have hh := (hB.sub hA).const_mul β
  simp only [sub_self,mul_zero] at hh
  apply hh.congr
  intro k
  ring

lemma total_normalized_budget (A B T : Finset ℕ) (hT : T.Nonempty)
    (δ L R β : ℝ) (hL : 0<L) (hR : 0<R)
    (hgain : ∀ n∈T, (sumRep (A : Set ℕ) n : ℝ)+δ*L ≤ sumRep (B : Set ℕ) n) :
    δ ≤ β*((B.card : ℝ)-A.card)/R+
      Real.sqrt ((((A.card : ℝ)+B.card)/R)*normalizedEnergy A B T L R β) := by
  apply (normalized_gain_energy_budget A B T hT δ L R β hL hR hgain).trans
  apply add_le_add le_rfl
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (editCount_le_total A B) hR.le)
    (normalizedEnergy_nonneg A B T L R β hR.le)

/-- If the normalized edit mass and energy have limits d and e, persistent
uniform gains force δ² <= d e. The center β is arbitrary. -/
theorem same_mass_energy_limit_floor (A B T : ℕ → Finset ℕ) (R L : ℕ → ℝ)
    (a δ β d e : ℝ) (hδ : 0<δ)
    (hA : Tendsto (fun k ↦ ((A k).card : ℝ)/R k) atTop (𝓝 a))
    (hB : Tendsto (fun k ↦ ((B k).card : ℝ)/R k) atTop (𝓝 a))
    (hD : Tendsto (fun k ↦ editCount (A k) (B k)/R k) atTop (𝓝 d))
    (hE : Tendsto (fun k ↦ normalizedEnergy (A k) (B k) (T k) (L k) (R k) β)
      atTop (𝓝 e))
    (hdata : ∀ᶠ k in atTop, 0<L k ∧ 0<R k ∧ (T k).Nonempty ∧
      (∀ n∈T k, (sumRep (A k : Set ℕ) n : ℝ)+δ*L k ≤ sumRep (B k : Set ℕ) n)) :
    δ^2≤d*e := by
  have hh := (cardinal_center_tendsto A B R a β hA hB).add ((hD.mul hE).sqrt)
  simp only [zero_add] at hh
  have hb : δ≤Real.sqrt (d*e) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hh
    filter_upwards [hdata] with k hk
    exact normalized_gain_energy_budget (A k) (B k) (T k) hk.2.2.1 δ (L k) (R k) β
      hk.1 hk.2.1 hk.2.2.2
  have hp : 0<d*e := Real.sqrt_pos.mp (hδ.trans_le hb)
  have hs := (sq_le_sq₀ hδ.le (Real.sqrt_nonneg _)).mpr hb
  simpa only [Real.sq_sqrt hp.le] using hs

/-- No limit of the symmetric difference is needed for the weaker factor
2a; arbitrary full replacement is allowed. -/
theorem same_mass_total_energy_limit_floor (A B T : ℕ → Finset ℕ) (R L : ℕ → ℝ)
    (a δ β e : ℝ) (hδ : 0<δ)
    (hA : Tendsto (fun k ↦ ((A k).card : ℝ)/R k) atTop (𝓝 a))
    (hB : Tendsto (fun k ↦ ((B k).card : ℝ)/R k) atTop (𝓝 a))
    (hE : Tendsto (fun k ↦ normalizedEnergy (A k) (B k) (T k) (L k) (R k) β)
      atTop (𝓝 e))
    (hdata : ∀ᶠ k in atTop, 0<L k ∧ 0<R k ∧ (T k).Nonempty ∧
      (∀ n∈T k, (sumRep (A k : Set ℕ) n : ℝ)+δ*L k ≤ sumRep (B k : Set ℕ) n)) :
    δ^2≤2*a*e := by
  have hmass : Tendsto (fun k ↦ (((A k).card : ℝ)+(B k).card)/R k) atTop (𝓝 (2*a)) := by
    simpa only [add_div,two_mul] using hA.add hB
  have hh := (cardinal_center_tendsto A B R a β hA hB).add ((hmass.mul hE).sqrt)
  simp only [zero_add] at hh
  have hb : δ≤Real.sqrt (2*a*e) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hh
    filter_upwards [hdata] with k hk
    exact total_normalized_budget (A k) (B k) (T k) hk.2.2.1 δ (L k) (R k) β
      hk.1 hk.2.1 hk.2.2.2
  have hp : 0<2*a*e := Real.sqrt_pos.mp (hδ.trans_le hb)
  have hs := (sq_le_sq₀ hδ.le (Real.sqrt_nonneg _)).mpr hb
  simpa only [Real.sq_sqrt hp.le] using hs

/-- Vanishing aggregate incidence energy, rather than uniform pointwise
regularity, prevents a same-density repair of persistent deficits. -/
theorem same_mass_vanishing_energy_empty (A B T : ℕ → Finset ℕ) (R L : ℕ → ℝ)
    (a δ β : ℝ) (hδ : 0<δ)
    (hA : Tendsto (fun k ↦ ((A k).card : ℝ)/R k) atTop (𝓝 a))
    (hB : Tendsto (fun k ↦ ((B k).card : ℝ)/R k) atTop (𝓝 a))
    (hE : Tendsto (fun k ↦ normalizedEnergy (A k) (B k) (T k) (L k) (R k) β)
      atTop (𝓝 0))
    (hdata : ∀ᶠ k in atTop, 0<L k ∧ 0<R k ∧
      (∀ n∈T k, (sumRep (A k : Set ℕ) n : ℝ)+δ*L k ≤ sumRep (B k : Set ℕ) n)) :
    ∀ᶠ k in atTop, T k=∅ := by
  have hmass : Tendsto (fun k ↦ (((A k).card : ℝ)+(B k).card)/R k) atTop (𝓝 (a+a)) := by
    simpa only [add_div] using hA.add hB
  have hh := (cardinal_center_tendsto A B R a β hA hB).add ((hmass.mul hE).sqrt)
  simp only [mul_zero,Real.sqrt_zero,zero_add] at hh
  filter_upwards [hdata,hh.eventually_lt_const hδ] with k hk hlt
  by_contra he
  have hb := total_normalized_budget (A k) (B k) (T k) (Finset.nonempty_iff_ne_empty.mpr he)
    δ (L k) (R k) β hk.1 hk.2.1 hk.2.2
  exact (not_lt_of_ge hb) hlt

/-- Negligible edit mass forces the normalized contrast energy past EVERY
fixed bound whenever targets persist. No convergence of this energy is
assumed, and the conclusion is conditional only on target nonemptiness. -/
theorem small_edits_require_unbounded_energy (A B T : ℕ → Finset ℕ) (R L : ℕ → ℝ)
    (a δ β : ℝ) (hδ : 0<δ)
    (hA : Tendsto (fun k ↦ ((A k).card : ℝ)/R k) atTop (𝓝 a))
    (hB : Tendsto (fun k ↦ ((B k).card : ℝ)/R k) atTop (𝓝 a))
    (hD : Tendsto (fun k ↦ editCount (A k) (B k)/R k) atTop (𝓝 0))
    (hdata : ∀ᶠ k in atTop, 0<L k ∧ 0<R k ∧
      (∀ n∈T k, (sumRep (A k : Set ℕ) n : ℝ)+δ*L k ≤ sumRep (B k : Set ℕ) n)) :
    ∀ M : ℝ, ∀ᶠ k in atTop, (T k).Nonempty →
      M<normalizedEnergy (A k) (B k) (T k) (L k) (R k) β := by
  intro M
  have hh := (cardinal_center_tendsto A B R a β hA hB).add ((hD.mul_const M).sqrt)
  simp only [zero_mul,Real.sqrt_zero,zero_add] at hh
  filter_upwards [hdata,hh.eventually_lt_const hδ] with k hk hlt
  intro hTk
  by_contra he
  have hEM : normalizedEnergy (A k) (B k) (T k) (L k) (R k) β≤M := le_of_not_gt he
  have hb := normalized_gain_energy_budget (A k) (B k) (T k) hTk δ (L k) (R k) β
    hk.1 hk.2.1 hk.2.2
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hEM
    (div_nonneg (editCount_nonneg (A k) (B k)) hk.2.1.le))
  linarith

end Erdos66SignedRepairEnergyStability
