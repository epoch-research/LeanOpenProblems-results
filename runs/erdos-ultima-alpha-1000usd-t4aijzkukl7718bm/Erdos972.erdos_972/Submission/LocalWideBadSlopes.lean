import Submission.LocalWeightedRationalArcs
import Submission.WideMetricSieve

/-! Local rational-exceptional-set bounds at an approximated irrational slope. -/
namespace Erdos972LocalWideBadSlopes

open Set Finset MeasureTheory
open Erdos972LocalRationalArcMeasure Erdos972LocalWeightedRationalArcs
open Erdos972WideMetricSieve Erdos972MetricSieve

noncomputable def wideRationalSet (A L : ℕ) : Finset ℚ :=
  (Finset.Ioc 0 L).biUnion fun q => (Finset.Icc 0 ((A + 2) * q)).image fun a : ℕ => mkRat (a : ℤ) q

lemma mkRat_den_le (a : ℕ) {q : ℕ} (hq : 0 < q) : (mkRat a q).den ≤ q := by
  rw [Rat.den_mkRat, if_neg (by omega)]
  exact Nat.div_le_self _ _

lemma wideRationalSet_den_le {A L : ℕ} {r : ℚ} (hr : r ∈ wideRationalSet A L) :
    r.den ≤ L := by
  obtain ⟨q, hq, hr⟩ := mem_biUnion.mp hr
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hr
  exact (mkRat_den_le a (mem_Ioc.mp hq).1).trans (mem_Ioc.mp hq).2

lemma wideBadSlopes_subset_rationalArcs (A L : ℕ) {Q : ℕ} (hQ : 0 < Q) :
    wideBadSlopes A L Q ⊆ ⋃ r ∈ wideRationalSet A L, rationalArc (Q : ℝ) r := by
  intro β hβ
  obtain ⟨q, hq, hβ⟩ := mem_iUnion₂.mp hβ
  obtain ⟨a, ha, hβ⟩ := mem_iUnion₂.mp hβ
  have hq0 := (Finset.mem_Ioc.mp hq).1
  have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hd : ((mkRat a q).den : ℝ) ≤ q := Nat.cast_le.mpr (mkRat_den_le a hq0)
  have hd0 : (0 : ℝ) < (mkRat a q).den := Nat.cast_pos.mpr (mkRat a q).pos
  have hrad : 1 / ((Q : ℝ) * q) ≤ 1 / ((Q : ℝ) * (mkRat a q).den) :=
    one_div_le_one_div_of_le (mul_pos hQR hd0) (mul_le_mul_of_nonneg_left hd hQR.le)
  apply mem_iUnion₂.mpr
  refine ⟨mkRat a q, mem_biUnion.mpr ⟨q, hq, mem_image.mpr ⟨a, ha, rfl⟩⟩, ?_⟩
  have hc : ((mkRat a q : ℚ) : ℝ) = (a : ℝ) / q := by simp [Rat.mkRat_eq_div]
  change (a : ℝ) / q - 1 / ((Q : ℝ) * q) ≤ β ∧
    β ≤ (a : ℝ) / q + 1 / ((Q : ℝ) * q) at hβ
  change ((mkRat a q : ℚ) : ℝ) - 1 / ((Q : ℝ) * (mkRat a q).den) ≤ β ∧
    β ≤ ((mkRat a q : ℚ) : ℝ) + 1 / ((Q : ℝ) * (mkRat a q).den)
  rw [hc]
  constructor <;> linarith [hβ.1, hβ.2]

lemma low_denominator_disjoint {α ε h D Q : ℝ} (r : ℚ)
    (hε : 0 ≤ ε) (hh : 0 < h) (hD : 0 < D) (hQ : 0 < Q)
    (happrox : |α - r| ≤ ε) (hrD : D < (r.den : ℝ))
    (hsmall : (ε + h) * D + 1 / Q < 1 / (r.den : ℝ))
    (s : ℚ) (hsD : (s.den : ℝ) ≤ D) :
    Disjoint (Ioo (α - h) α) (rationalArc Q s) := by
  apply Set.disjoint_left.mpr
  intro β hβ hβs
  have hr0 : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hs0 : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hrs : r ≠ s := by
    intro he
    subst s
    linarith
  have hsep := rational_separation hrs
  have hβs' : |β - (s : ℝ)| ≤ 1 / (Q * s.den) := by
    apply abs_le.mpr
    constructor <;> linarith [hβs.1, hβs.2]
  have hαβ : |α - β| ≤ h := by
    rw [abs_of_pos (sub_pos.mpr hβ.2)]
    linarith [hβ.1]
  have hdist : |(r : ℝ) - s| ≤ ε + h + 1 / (Q * s.den) := by
    calc
      _ ≤ |(r : ℝ) - α| + |α - β| + |β - (s : ℝ)| := by
        have h₁ := abs_sub_le (r : ℝ) α β
        have h₂ := abs_sub_le (r : ℝ) β (s : ℝ)
        linarith
      _ ≤ _ := by rw [abs_sub_comm (r : ℝ) α]; gcongr
  have hprod := mul_le_mul_of_nonneg_right (hsep.trans hdist) hs0.le
  have hleft : 1 / ((r.den : ℝ) * s.den) * s.den = 1 / (r.den : ℝ) := by field_simp
  have hright : (ε + h + 1 / (Q * s.den)) * s.den =
      (ε + h) * s.den + 1 / Q := by field_simp
  rw [hleft, hright] at hprod
  have hmono := mul_le_mul_of_nonneg_left hsD (by positivity : 0 ≤ ε + h)
  linarith

/-- A local upper bound for the actual exceptional sets used by the sieve.
The low-denominator part is absent by separation from one approximant; all
remaining reduced denominators are handled by variable-radius packing. -/
theorem local_wideBadSlopes_measure {α ε h D : ℝ} (r : ℚ) (A L Q : ℕ)
    (hε : 0 ≤ ε) (hh : 0 < h) (hD : 0 < D) (hL : 0 < L) (hQ : 0 < Q)
    (happrox : |α - r| ≤ ε) (hrD : D < (r.den : ℝ))
    (hsmall : (ε + h) * D + 1 / (Q : ℝ) < 1 / (r.den : ℝ)) :
    volume.real (Ioo (α - h) α ∩ wideBadSlopes A L Q) ≤
      (2 * (L : ℝ) / Q) * h + 4 * L / ((Q : ℝ)^2 * D) + 2 / ((Q : ℝ) * D) := by
  classical
  let S := (wideRationalSet A L).filter fun s => D ≤ (s.den : ℝ)
  have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hsub : (Ioo (α - h) α ∩ wideBadSlopes A L Q) ⊆
      Ioo (α - h) α ∩ ⋃ s ∈ S, rationalArc (Q : ℝ) s := by
    intro β hβ
    obtain ⟨s, hs, hβs⟩ := mem_iUnion₂.mp (wideBadSlopes_subset_rationalArcs A L hQ hβ.2)
    have hsD : D ≤ (s.den : ℝ) := by
      by_contra hn
      have hd := low_denominator_disjoint r hε hh hD hQR happrox hrD hsmall s
        (le_of_not_ge hn)
      exact Set.disjoint_left.mp hd hβ.1 hβs
    exact ⟨hβ.1, mem_iUnion₂.mpr ⟨s, mem_filter.mpr ⟨hs, hsD⟩, hβs⟩⟩
  have hfin : volume (Ioo (α - h) α ∩ ⋃ s ∈ S, rationalArc (Q : ℝ) s) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Ioo (α - h) α) ≠ ⊤ by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    exact measure_mono inter_subset_left
  have hbound := rational_range_local_measure S (show α - h ≤ α by linarith) hD
    (Nat.cast_pos.mpr hL) hQR (fun s hs =>
      ⟨(mem_filter.mp hs).2, Nat.cast_le.mpr (wideRationalSet_den_le (mem_filter.mp hs).1)⟩)
  have hm := (measureReal_mono hsub hfin).trans hbound
  convert hm using 1 <;> ring

#print axioms local_wideBadSlopes_measure
end Erdos972LocalWideBadSlopes
