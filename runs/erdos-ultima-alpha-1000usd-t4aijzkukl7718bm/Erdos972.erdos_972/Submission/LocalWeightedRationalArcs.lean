import Submission.LocalRationalArcMeasure

/-! Variable-radius packing for local rational exceptional sets. -/
namespace Erdos972LocalWeightedRationalArcs

open Set Finset MeasureTheory
open Erdos972LocalRationalArcMeasure

/-- The reciprocal-denominator packing intervals are disjoint. -/
lemma packing_disjoint (S : Finset ℚ) {L : ℝ} (hL : 0 < L)
    (hden : ∀ r ∈ S, (r.den : ℝ) ≤ L) :
    Set.PairwiseDisjoint (↑S : Set ℚ)
      (fun r => Ioo ((r : ℝ) - 1 / (2 * L * r.den))
        ((r : ℝ) + 1 / (2 * L * r.den))) := by
  intro r hr s hs hrs
  apply Set.disjoint_left.mpr
  intro β hβr hβs
  have hr0 : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hs0 : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hsep := rational_separation hrs
  have hrad : 1 / (2 * L * r.den) + 1 / (2 * L * s.den) ≤
      1 / ((r.den : ℝ) * s.den) := by
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * L * (r.den : ℝ) * s.den by positivity)).mp
    field_simp
    nlinarith [hden r hr, hden s hs]
  have hdist : |(r : ℝ) - s| < 1 / (2 * L * r.den) + 1 / (2 * L * s.den) := by
    apply abs_lt.mpr
    constructor <;> linarith [hβr.1, hβr.2, hβs.1, hβs.2]
  exact (not_lt_of_ge hsep) (hdist.trans_le hrad)

/-- All reduced denominators in `[D,L]` can be treated in a single packing.
Both endpoint terms are retained. -/
theorem rational_range_local_measure (S : Finset ℚ) {a b D L Q : ℝ}
    (hab : a ≤ b) (hD : 0 < D) (hL : 0 < L) (hQ : 0 < Q)
    (hden : ∀ r ∈ S, D ≤ (r.den : ℝ) ∧ (r.den : ℝ) ≤ L) :
    volume.real (Ioo a b ∩ ⋃ r ∈ S, rationalArc Q r) ≤
      (2 * L / Q) * (b - a) + 4 * L / (Q ^ 2 * D) + 2 / (Q * D) := by
  classical
  let R : ℝ := 1 / (Q * D)
  let P : ℝ := 1 / (2 * L * D)
  let T : Finset ℚ := S.filter (fun r => a - R ≤ (r : ℝ) ∧ (r : ℝ) ≤ b + R)
  let U : ℚ → Set ℝ := fun r => Ioo ((r : ℝ) - 1 / (2 * L * r.den))
    ((r : ℝ) + 1 / (2 * L * r.den))
  have hR : 0 < R := by dsimp [R]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hradius (r : ℚ) (hr : r ∈ S) : 1 / (Q * (r.den : ℝ)) ≤ R := by
    exact one_div_le_one_div_of_le (mul_pos hQ hD)
      (mul_le_mul_of_nonneg_left (hden r hr).1 hQ.le)
  have hpacking (r : ℚ) (hr : r ∈ S) : 1 / (2 * L * (r.den : ℝ)) ≤ P := by
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (hden r hr).1 (by positivity))
  have hsub : (Ioo a b ∩ ⋃ r ∈ S, rationalArc Q r) ⊆ ⋃ r ∈ T, rationalArc Q r := by
    intro β hβ
    obtain ⟨r, hr, hβr⟩ := mem_iUnion₂.mp hβ.2
    have hbds : (r : ℝ) - 1 / (Q * r.den) ≤ β ∧ β ≤ (r : ℝ) + 1 / (Q * r.den) := hβr
    have hrad := hradius r hr
    apply mem_iUnion₂.mpr
    refine ⟨r, mem_filter.mpr ⟨hr, ?_⟩, hβr⟩
    constructor <;> linarith [hβ.1.1, hβ.1.2]
  have hpacksub : (⋃ r ∈ T, U r) ⊆ Ioo (a - R - P) (b + R + P) := by
    intro β hβ
    obtain ⟨r, hr, hβr⟩ := mem_iUnion₂.mp hβ
    obtain ⟨hrS, hlo, hhi⟩ := mem_filter.mp hr
    have hrad := hpacking r hrS
    change (r : ℝ) - 1 / (2 * L * r.den) < β ∧
      β < (r : ℝ) + 1 / (2 * L * r.den) at hβr
    constructor <;> linarith [hβr.1, hβr.2]
  have hdisj : Set.PairwiseDisjoint (↑T : Set ℚ) U :=
    packing_disjoint T hL (fun r hr => (hden r (mem_filter.mp hr).1).2)
  have humeas (r : ℚ) : volume.real (U r) = 1 / (L * r.den) := by
    dsimp [U]
    rw [Real.volume_real_Ioo,
      show (r : ℝ) + 1 / (2 * L * r.den) - ((r : ℝ) - 1 / (2 * L * r.den)) =
        1 / (L * r.den) by ring,
      max_eq_left (by positivity)]
  have hpack : (∑ r ∈ T, 1 / (L * (r.den : ℝ))) ≤ b - a + 2 * R + 2 * P := by
    have hm := measureReal_mono hpacksub
      (show volume (Ioo (a - R - P) (b + R + P)) ≠ ⊤ by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    rw [measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_Ioo)
      (fun r _ => by dsimp [U]; rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top),
      Real.volume_real_Ioo,
      show b + R + P - (a - R - P) = b - a + 2 * R + 2 * P by ring,
      max_eq_left (by linarith)] at hm
    simpa only [humeas] using hm
  have hfin : volume (⋃ r ∈ T, rationalArc Q r) ≠ ⊤ :=
    (T.isCompact_biUnion (fun r _ => isCompact_Icc)).measure_lt_top.ne
  calc
    _ ≤ ∑ r ∈ T, volume.real (rationalArc Q r) :=
      (measureReal_mono hsub hfin).trans (measureReal_biUnion_finset_le T _)
    _ = (2 * L / Q) * ∑ r ∈ T, 1 / (L * (r.den : ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      rw [rationalArc_measure hQ]
      field_simp
    _ ≤ (2 * L / Q) * (b - a + 2 * R + 2 * P) :=
      mul_le_mul_of_nonneg_left hpack (by positivity)
    _ = _ := by
      dsimp [R, P]
      field_simp
      ring

#print axioms packing_disjoint
#print axioms rational_range_local_measure
end Erdos972LocalWeightedRationalArcs
