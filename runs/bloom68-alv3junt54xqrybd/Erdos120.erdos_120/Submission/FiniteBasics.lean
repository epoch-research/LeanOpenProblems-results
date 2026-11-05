import FormalConjecturesUtil
import Submission.Reductions

/-!
# Finite real patterns cannot be avoided

Every measurable real set of positive volume contains a nonzero affine copy of
any finite real set, including the empty set. In fact, every sufficiently small
slope admits a suitable translation, and the slope may be chosen positive.

The measure argument first passes to a compact positive-volume subset of the
target. Translation continuity makes each of the finitely many translation losses
tend to zero. Their finite sum bounds the loss in the intersection, which therefore
has positive volume for all sufficiently small slopes.

The final equivalences only reformulate the infinite-set avoidance conjecture and
its negation. They do not prove or disprove it. This file is independent of
`Submission.Spec` and does not assert non-avoidance of any infinite set.
-/

open Set MeasureTheory Filter
open scoped Topology Pointwise ENNReal

namespace Erdos120Aux

/-- The volume lost from a compact set when imposing one small translation
constraint tends to zero. Translation invariance reverses the set difference so
that Mathlib's compact-translation continuity theorem applies. -/
private theorem tendsto_volume_compact_translation_loss {K : Set ℝ}
    (hK : IsCompact K) (x : ℝ) :
    Tendsto (fun a : ℝ => volume (K \ (-(a * x) +ᵥ K))) (𝓝 0) (𝓝 0) := by
  simp_rw [measure_sdiff_neg_vadd]
  have hmul : Tendsto (fun a : ℝ => a * x) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_id.mul continuous_const).tendsto (0 : ℝ)
  exact (tendsto_measure_vadd_diff_isCompact_isClosed (μ := volume) hK hK.isClosed).comp
    hmul

/-- For a finite pattern and a compact positive-volume target, the translations
placing the pattern in the target have positive volume at every sufficiently
small slope. We additionally restrict the translation parameter to the target.
No nonemptiness assumption on the pattern is needed. -/
theorem eventually_positive_volume_finite_affine_translations {A K : Set ℝ}
    (hA : A.Finite) (hK : IsCompact K) (hpos : 0 < volume K) :
    ∀ᶠ a : ℝ in 𝓝 0,
      0 < volume {b : ℝ | b ∈ K ∧ Set.image (fun x => a * x + b) A ⊆ K} := by
  classical
  have hsum : Tendsto
      (fun a : ℝ => ∑ x ∈ hA.toFinset, volume (K \ (-(a * x) +ᵥ K)))
      (𝓝 0) (𝓝 0) := by
    simpa using tendsto_finset_sum hA.toFinset
      (fun x _ => tendsto_volume_compact_translation_loss hK x)
  filter_upwards [hsum.eventually (eventually_lt_nhds hpos)] with a ha
  let B : Set ℝ := ⋃ x ∈ hA.toFinset, K \ (-(a * x) +ᵥ K)
  have hB : volume B < volume K :=
    (measure_biUnion_finset_le hA.toFinset (fun x => K \ (-(a * x) +ᵥ K))).trans_lt ha
  have hgood : K \ B ⊆
      {b : ℝ | b ∈ K ∧ Set.image (fun x => a * x + b) A ⊆ K} := by
    rintro b ⟨hbK, hbB⟩
    refine ⟨hbK, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxfin : x ∈ hA.toFinset := hA.mem_toFinset.mpr hx
    have hbtrans : b ∈ -(a * x) +ᵥ K := by
      by_contra hb
      exact hbB (mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxfin, ⟨hbK, hb⟩⟩⟩)
    exact mem_neg_vadd_set_iff.mp hbtrans
  calc
    0 < volume K - volume B := tsub_pos_iff_lt.mpr hB
    _ ≤ volume (K \ B) := le_measure_diff
    _ ≤ volume {b : ℝ | b ∈ K ∧ Set.image (fun x => a * x + b) A ⊆ K} :=
      measure_mono hgood

/-- Every sufficiently small slope permits an affine copy of a finite pattern
inside a measurable positive-volume real target. The target need not have finite
volume, because we work inside a compact positive-volume subset. -/
theorem eventually_exists_affine_image_subset_of_finite {A E : Set ℝ}
    (hA : A.Finite) (hE : MeasurableSet E) (hpos : 0 < volume E) :
    ∀ᶠ a : ℝ in 𝓝 0, ∃ b : ℝ, Set.image (fun x => a * x + b) A ⊆ E := by
  obtain ⟨K, hKE, hK, hposK, _⟩ := exists_compact_positive_subset hE hpos
  filter_upwards [eventually_positive_volume_finite_affine_translations hA hK hposK]
    with a ha
  obtain ⟨b, _, hb⟩ := nonempty_of_measure_ne_zero ha.ne'
  exact ⟨b, hb.trans hKE⟩

/-- A finite real pattern embeds in every measurable positive-volume target with
strictly positive slope. This includes empty and singleton patterns. -/
theorem exists_pos_affine_image_subset_of_finite {A E : Set ℝ}
    (hA : A.Finite) (hE : MeasurableSet E) (hpos : 0 < volume E) :
    ∃ a b : ℝ, 0 < a ∧ Set.image (fun x => a * x + b) A ⊆ E := by
  have hembed : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      ∃ b : ℝ, Set.image (fun x => a * x + b) A ⊆ E :=
    (eventually_exists_affine_image_subset_of_finite hA hE hpos).filter_mono
      nhdsWithin_le_nhds
  have hpositive : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  obtain ⟨a, ha, b, hb⟩ := (hpositive.and hembed).exists
  exact ⟨a, b, ha, hb⟩

/-- The nonzero-slope formulation of finite-pattern embedding, with exactly the
affine maps appearing in `Avoidance`. -/
theorem exists_affine_image_subset_of_finite {A E : Set ℝ}
    (hA : A.Finite) (hE : MeasurableSet E) (hpos : 0 < volume E) :
    ∃ a b : ℝ, a ≠ 0 ∧ Set.image (fun x => a * x + b) A ⊆ E := by
  obtain ⟨a, b, ha, hb⟩ := exists_pos_affine_image_subset_of_finite hA hE hpos
  exact ⟨a, b, ha.ne', hb⟩

/-- No finite real set has a measurable positive-volume avoidance witness. -/
theorem not_avoidance_of_finite {A : Set ℝ} (hA : A.Finite) : ¬ Avoidance A := by
  rintro ⟨E, hE, hpos, havoid⟩
  obtain ⟨a, b, ha, hb⟩ := exists_affine_image_subset_of_finite hA hE hpos
  exact havoid a b ha hb

/-- In particular, the empty pattern cannot be avoided. -/
@[simp] theorem not_avoidance_empty : ¬ Avoidance (∅ : Set ℝ) :=
  not_avoidance_of_finite Set.finite_empty

/-- In particular, no singleton pattern can be avoided. -/
@[simp] theorem not_avoidance_singleton (x : ℝ) : ¬ Avoidance ({x} : Set ℝ) :=
  not_avoidance_of_finite (Set.finite_singleton x)

/-- Having an avoidance witness forces a real source set to be infinite. The
converse for all infinite source sets is precisely the unresolved conjecture. -/
theorem Avoidance.infinite {A : Set ℝ} (hA : Avoidance A) : A.Infinite := by
  intro hfinite
  exact not_avoidance_of_finite hfinite hA

/-- Purely a quantifier connection: universal avoidance of infinite real sets is
equivalent to the absence of an infinite non-avoidable set. Neither side is
asserted here; no theorem from `Submission.Spec` is used. -/
theorem infinite_avoidance_conjecture_iff_no_counterexample :
    (∀ A : Set ℝ, A.Infinite → Avoidance A) ↔
      ¬ ∃ A : Set ℝ, A.Infinite ∧ ¬ Avoidance A := by
  classical
  constructor
  · intro h ⟨A, hAI, hnot⟩
    exact hnot (h A hAI)
  · intro h A hAI
    by_contra hnot
    exact h ⟨A, hAI, hnot⟩

/-- Purely the negated quantifier connection: failure of the general infinite-set
avoidance statement is equivalent to an infinite non-avoidance counterexample. -/
theorem not_infinite_avoidance_conjecture_iff_exists_counterexample :
    ¬ (∀ A : Set ℝ, A.Infinite → Avoidance A) ↔
      ∃ A : Set ℝ, A.Infinite ∧ ¬ Avoidance A := by
  classical
  push_neg
  rfl

/-- The finite case proves the necessary direction of this classification. The
sufficiency direction for infinite sets is still exactly the general conjecture. -/
theorem infinite_avoidance_conjecture_iff_avoidance_iff_infinite :
    (∀ A : Set ℝ, A.Infinite → Avoidance A) ↔
      ∀ A : Set ℝ, Avoidance A ↔ A.Infinite := by
  constructor
  · intro h A
    exact ⟨Avoidance.infinite, h A⟩
  · intro h A hAI
    exact (h A).mpr hAI

end Erdos120Aux
