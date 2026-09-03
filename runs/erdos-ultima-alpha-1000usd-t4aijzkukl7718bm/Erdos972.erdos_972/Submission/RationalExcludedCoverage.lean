import Submission.LocalRationalHoleScales
import Submission.OneSidedPrimePairHole

/-! A common-scale obstruction for the zero-count set itself. Unlike a
linear lower-tail moment target, this only asks whether any pair occurs. -/
namespace Erdos972RationalExcludedCoverage

open Set MeasureTheory Filter
open scoped Topology
open Erdos972Topology Erdos972OneSidedPrimePairHole
open Erdos972WideMetricSieve Erdos972LocalRationalHoleScales

lemma excluded_missing_measure_lower {a b α : ℝ} {B N : ℕ} {E : Set ℝ}
    (hN : 0 < N) (hE : MeasurableSet E)
    (ha : a ≤ α - 1 / (2 * (N : ℝ))) (hb : α ≤ b)
    (hno : ∀ p ∈ primeSet α, p ≤ B)
    (hloss : volume.real (Ioo (α - 1 / (2 * (N : ℝ))) α ∩ E) ≤ 1 / (4 * (N : ℝ))) :
    1 / (4 * (N : ℝ)) ≤ volume.real (Ioo a b \ (narrowTail B N ∪ E)) := by
  have hadd := measureReal_inter_add_diff (μ := volume)
    (s := Ioo (α - 1 / (2 * (N : ℝ))) α) hE
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  rw [left_interval_measure hN] at hadd
  have hremain : 1 / (4 * (N : ℝ)) ≤
      volume.real (Ioo (α - 1 / (2 * (N : ℝ))) α \ E) := by
    have he : 1 / (2 * (N : ℝ)) = 2 * (1 / (4 * (N : ℝ))) := by ring
    linarith
  have hsub : (Ioo (α - 1 / (2 * (N : ℝ))) α \ E) ⊆
      Ioo a b \ (narrowTail B N ∪ E) := by
    intro β hβ
    refine ⟨⟨ha.trans_lt hβ.1.1, hβ.1.2.trans_le hb⟩, ?_⟩
    intro hh
    rcases hh with hh | hh
    · exact left_interval_subset_compl hN hno hβ.1 hh
    · exact hβ.2 hh
  have hfin : volume (Ioo a b \ (narrowTail B N ∪ E)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Ioo a b) ≠ ⊤ by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    exact measure_mono diff_subset
  exact hremain.trans (measureReal_mono hsub hfin)

/-- Finiteness leaves a `1/(4N)` zero-count set outside the actual rational
exclusions at arbitrarily large common metric scales. -/
theorem finite_primeSet_forces_excluded_missing {α a b : ℝ} (A : ℕ)
    (hα : 1 < α) (hI : Irrational α) (ha : a < α) (hb : α < b)
    (hfin : (primeSet α).Finite) :
    ∃ B : ℕ, ∀ V : ℕ, ∃ v : ℕ, V < v ∧ 2 ≤ v ∧ A ≤ v ∧
      1 / (4 * ((v^40 : ℕ) : ℝ)) ≤
        volume.real (Ioo a b \ (narrowTail B (v^40) ∪ wideBadSlopes A (v^24) (v^28))) := by
  obtain ⟨B, hB⟩ := hfin.bddAbove
  have he : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) / N < α - a :=
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))).2
      (α - a) (sub_pos.mpr ha)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  refine ⟨B, fun V => ?_⟩
  obtain ⟨v, hv, hv2, hloss⟩ := exists_half_hole_scale hα hI A (max V (max N₀ A))
  have hVv : V < v := (le_max_left _ _).trans_lt hv
  have hNv : N₀ ≤ v := ((le_max_left N₀ A).trans (le_max_right V _)).trans hv.le
  have hAv : A ≤ v := ((le_max_right N₀ A).trans (le_max_right V _)).trans hv.le
  have hvpow : v ≤ v^40 := by
    simpa using Nat.pow_le_pow_right (show 0 < v by omega) (show 1 ≤ 40 by omega)
  have hh := hN₀ (v^40) (hNv.trans hvpow)
  rw [div_div] at hh
  refine ⟨v, hVv, hv2, hAv, excluded_missing_measure_lower (by positivity)
    (measurableSet_wideBadSlopes _ _ _) (by linarith) hb.le hB hloss⟩

/-- A strict finite-scale coverage estimate suffices. The estimate is an
explicit hypothesis here, not an established arithmetic theorem. -/
theorem infinite_of_eventually_small_excluded_missing {α a b : ℝ} (A : ℕ)
    (hα : 1 < α) (hI : Irrational α) (ha : a < α) (hb : α < b)
    (hcoverage : ∀ B : ℕ, ∀ᶠ v : ℕ in atTop,
      volume.real (Ioo a b \ (narrowTail B (v^40) ∪ wideBadSlopes A (v^24) (v^28))) <
        1 / (4 * ((v^40 : ℕ) : ℝ))) :
    (primeSet α).Infinite := by
  by_contra hn
  obtain ⟨B, hB⟩ := finite_primeSet_forces_excluded_missing A hα hI ha hb (Set.not_infinite.mp hn)
  obtain ⟨V, hV⟩ := eventually_atTop.mp (hcoverage B)
  obtain ⟨v, hv, _, _, hlower⟩ := hB V
  exact (not_lt_of_ge hlower) (hV v hv.le)

#print axioms finite_primeSet_forces_excluded_missing
#print axioms infinite_of_eventually_small_excluded_missing
end Erdos972RationalExcludedCoverage
