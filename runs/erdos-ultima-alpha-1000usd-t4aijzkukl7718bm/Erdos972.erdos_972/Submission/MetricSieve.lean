import Submission.PairSieve
import Submission.MetricRichness

/-!
Quantitative exceptional sets for the upper sieve. The rational neighborhoods
below have small measure; outside them the sieve can be used at a common cutoff.
-/
namespace Erdos972MetricSieve

open Finset MeasureTheory
open Erdos972RationalRotationCount Erdos972PairSieve

noncomputable def rationalBox (Q q a : ℕ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - 1 / ((Q : ℝ) * q)) ((a : ℝ) / q + 1 / ((Q : ℝ) * q))

noncomputable def badSlopes (L Q : ℕ) : Set ℝ :=
  ⋃ q ∈ Ioc 0 L, ⋃ a ∈ Icc 0 (10 * q), rationalBox Q q a

lemma isCompact_badSlopes (L Q : ℕ) : IsCompact (badSlopes L Q) := by
  apply (Ioc 0 L).isCompact_biUnion
  intro q _
  apply (Icc 0 (10 * q)).isCompact_biUnion
  intro a _
  exact isCompact_Icc

lemma measurableSet_badSlopes (L Q : ℕ) : MeasurableSet (badSlopes L Q) :=
  (isCompact_badSlopes L Q).isClosed.measurableSet

lemma badSlopes_measure_ne_top (L Q : ℕ) : volume (badSlopes L Q) ≠ ⊤ :=
  (isCompact_badSlopes L Q).measure_lt_top.ne

lemma rationalBox_measure (Q q a : ℕ) :
    volume.real (rationalBox Q q a) = 2 / ((Q : ℝ) * q) := by
  rw [rationalBox, Real.volume_real_Icc]
  have h : (0 : ℝ) ≤ 1 / ((Q : ℝ) * q) := by positivity
  rw [show (a : ℝ) / q + 1 / ((Q : ℝ) * q) -
      ((a : ℝ) / q - 1 / ((Q : ℝ) * q)) = 2 / ((Q : ℝ) * q) by ring,
    max_eq_left (by positivity)]

lemma badSlopes_measure_le (L Q : ℕ) (hQ : 0 < Q) :
    volume.real (badSlopes L Q) ≤ 22 * L / (Q : ℝ) := by
  have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  unfold badSlopes
  apply (measureReal_biUnion_finset_le _ _).trans
  calc
    (∑ q ∈ Ioc 0 L, volume.real (⋃ a ∈ Icc 0 (10 * q), rationalBox Q q a)) ≤
        ∑ q ∈ Ioc 0 L, (22 : ℝ) / Q := by
      apply sum_le_sum
      intro q hq
      have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (mem_Ioc.mp hq).1
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Ioc.mp hq).1
      apply (measureReal_biUnion_finset_le _ _).trans
      simp only [rationalBox_measure, sum_const, nsmul_eq_mul, Nat.card_Icc,
        Nat.sub_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      apply (le_div_iff₀ hQR).mpr
      field_simp
      nlinarith
    _ = _ := by simp [mul_div_assoc, mul_comm]

lemma mem_badSlopes_of_approximant {α : ℝ} (hα : 1 < α) (hα9 : α < 9)
    {L Q : ℕ} (hQ : 0 < Q) (r : ℚ)
    (happrox : |α - r| ≤ 1 / ((Q : ℝ) * r.den)) (hrL : r.den ≤ L) :
    α ∈ badSlopes L Q := by
  have hq : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have he1 : 1 / ((Q : ℝ) * r.den) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have he := abs_le.mp (happrox.trans he1)
  have hr0 : 0 ≤ r := by exact_mod_cast (show (0 : ℝ) ≤ r by linarith)
  have hr10 : (r : ℝ) ≤ 10 := by linarith
  let a := r.num.natAbs
  have hra : (r : ℝ) = (a : ℝ) / r.den := nonneg_rat_cast_eq_natAbs_div r hr0
  have ha : a ≤ 10 * r.den := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    rw [hra] at hr10
    exact (div_le_iff₀ hq).mp hr10
  apply Set.mem_iUnion.mpr
  refine ⟨r.den, Set.mem_iUnion.mpr ⟨mem_Ioc.mpr ⟨r.pos, hrL⟩, ?_⟩⟩
  apply Set.mem_iUnion.mpr
  refine ⟨a, Set.mem_iUnion.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, ha⟩, ?_⟩⟩
  change (a : ℝ) / r.den - 1 / ((Q : ℝ) * r.den) ≤ α ∧
    α ≤ (a : ℝ) / r.den + 1 / ((Q : ℝ) * r.den)
  rw [← hra]
  obtain ⟨hlo, hhi⟩ := abs_le.mp happrox
  constructor <;> linarith

/-- Outside the explicit neighborhoods, Dirichlet approximation has a
controlled denominator bounded below as well as above. -/
lemma exists_approximant_of_not_mem_badSlopes {α : ℝ} (hα : 1 < α) (hα9 : α < 9)
    (L Q : ℕ) (hQ : 0 < Q) (hbad : α ∉ badSlopes L Q) :
    ∃ r : ℚ, 0 ≤ r ∧ L < r.den ∧ r.den ≤ Q ∧
      |α - r| ≤ 1 / ((Q : ℝ) * r.den) := by
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hQ
  have hq : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have happrox : |α - r| ≤ 1 / ((Q : ℝ) * r.den) := by
    apply hr.trans
    apply one_div_le_one_div_of_le (mul_pos hQR hq)
    nlinarith
  have hL : L < r.den := by
    by_contra h
    exact hbad (mem_badSlopes_of_approximant hα hα9 hQ r happrox (Nat.le_of_not_gt h))
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have he1 : 1 / ((Q : ℝ) * r.den) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have herror := (abs_le.mp (happrox.trans he1)).2
  have hr0 : 0 ≤ r := by exact_mod_cast (show (0 : ℝ) ≤ r by linarith)
  exact ⟨r, hr0, hL, hden, happrox⟩

#print axioms badSlopes_measure_le
#print axioms exists_approximant_of_not_mem_badSlopes

end Erdos972MetricSieve
