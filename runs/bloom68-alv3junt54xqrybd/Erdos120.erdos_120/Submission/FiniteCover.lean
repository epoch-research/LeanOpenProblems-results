import FormalConjecturesUtil
import Submission.CoveringReduction

/-!
# Finite hitting sets for compact affine parameter sets

An open set meeting each affine copy of `A` over a compact set of parameters
already does so using a finite subset of `A`. Applying this to the bounded
parameter rectangle and the covering reduction gives finite hitting sets with
arbitrarily small open targets, conditional on boundedness and avoidance of `A`.

The final contrapositive assumes a positive lower bound for the volume of every
open target hitting the rectangle. That lower bound is an explicit hypothesis,
not an assertion proved here. These results do not settle avoidance for arbitrary
bounded infinite sets and do not use the original conjecture statement.
-/

open Set MeasureTheory
open scoped ENNReal Topology

namespace Erdos120Aux

/-- An open target hitting every parameter in a compact set needs only finitely
many points of `A`. The open cover is indexed by the subtype `A`. -/
theorem exists_finite_subset_hitting_compact_parameters
    {A G : Set ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hG : IsOpen G)
    (hhit : ∀ p ∈ K, ∃ x ∈ A, p.1 * x + p.2 ∈ G) :
    ∃ F : Set ℝ, F.Finite ∧ F ⊆ A ∧
      ∀ p ∈ K, ∃ x ∈ F, p.1 * x + p.2 ∈ G := by
  classical
  let U : A → Set (ℝ × ℝ) := fun x =>
    (fun p : ℝ × ℝ => p.1 * (x : ℝ) + p.2) ⁻¹' G
  have hU : ∀ x : A, IsOpen (U x) := fun x =>
    hG.preimage ((continuous_fst.mul continuous_const).add continuous_snd)
  have hcover : K ⊆ ⋃ x : A, U x := by
    intro p hp
    obtain ⟨x, hxA, hxG⟩ := hhit p hp
    exact mem_iUnion.mpr ⟨⟨x, hxA⟩, hxG⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨Subtype.val '' (t : Set A), t.finite_toSet.image Subtype.val, ?_, ?_⟩
  · rintro x ⟨y, _, rfl⟩
    exact y.property
  · intro p hp
    obtain ⟨x, hxt, hxG⟩ := mem_iUnion₂.mp (ht hp)
    exact ⟨(x : ℝ), ⟨x, hxt, rfl⟩, hxG⟩

/-- Slopes in `[1, 2]` and translations in `[0, 1]`. -/
def boundedParameters : Set (ℝ × ℝ) :=
  Icc (1 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1

/-- The bounded affine parameter rectangle is compact. -/
theorem isCompact_boundedParameters : IsCompact boundedParameters :=
  isCompact_Icc.prod isCompact_Icc

/-- Specialization of the finite-subcover lemma to the bounded rectangle. -/
theorem exists_finite_subset_hitting_bounded_parameters
    {A G : Set ℝ} (hG : IsOpen G)
    (hhit : ∀ p ∈ boundedParameters, ∃ x ∈ A, p.1 * x + p.2 ∈ G) :
    ∃ F : Set ℝ, F.Finite ∧ F ⊆ A ∧
      ∀ p ∈ boundedParameters, ∃ x ∈ F, p.1 * x + p.2 ∈ G :=
  exists_finite_subset_hitting_compact_parameters isCompact_boundedParameters hG hhit

/-- A bounded set with avoidance admits an arbitrarily small open target that
hits every bounded parameter using a finite subset of the source set. Both the
finite subset and the open target may depend on the positive volume budget. -/
theorem Avoidance.exists_open_small_finite_hitting_set_bounded_parameters
    {A : Set ℝ} (havoid : Avoidance A) (hbounded : Bornology.IsBounded A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F G : Set ℝ, F.Finite ∧ F ⊆ A ∧ IsOpen G ∧
      volume G < ENNReal.ofReal ε ∧
      ∀ p ∈ boundedParameters, ∃ x ∈ F, p.1 * x + p.2 ∈ G := by
  obtain ⟨G, hG, hsmall, hhit⟩ :=
    havoid.exists_open_small_hitting_set_bounded_parameters hbounded hε
  have hhitP : ∀ p ∈ boundedParameters, ∃ x ∈ A, p.1 * x + p.2 ∈ G :=
    fun p hp => hhit p.1 p.2 hp.1 hp.2
  obtain ⟨F, hF, hFA, hhitF⟩ :=
    exists_finite_subset_hitting_bounded_parameters hG hhitP
  exact ⟨F, G, hF, hFA, hG, hsmall, hhitF⟩

/-- Conditional contrapositive of the bounded covering reduction. The existence
of a positive universal volume lower bound is the explicit hypothesis `H`; this
lemma does not assert that such a bound exists for any particular source set. -/
theorem not_avoidance_of_bounded_parameters_volume_lower_bound
    {A : Set ℝ} (hbounded : Bornology.IsBounded A)
    (H : ∃ δ : ℝ, 0 < δ ∧ ∀ G : Set ℝ, IsOpen G →
      (∀ p ∈ boundedParameters, ∃ x ∈ A, p.1 * x + p.2 ∈ G) →
        ENNReal.ofReal δ ≤ volume G) :
    ¬ Avoidance A := by
  intro havoid
  obtain ⟨δ, hδ, hlower⟩ := H
  obtain ⟨F, G, _, hFA, hG, hsmall, hhitF⟩ :=
    havoid.exists_open_small_finite_hitting_set_bounded_parameters hbounded hδ
  have hhitA : ∀ p ∈ boundedParameters, ∃ x ∈ A, p.1 * x + p.2 ∈ G := by
    intro p hp
    obtain ⟨x, hxF, hxG⟩ := hhitF p hp
    exact ⟨x, hFA hxF, hxG⟩
  exact (not_lt_of_ge (hlower G hG hhitA)) hsmall

end Erdos120Aux
