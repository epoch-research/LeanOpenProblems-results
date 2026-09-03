import Submission.LocallyFiniteFolkmanTarget

/-!
The countable generic K4-free target cannot map to any locally finitely
vertex-colorable graph. In particular it cannot be replaced by the locally
finite target having the same finite age. This distinguishes targets; it does
not assert that any generic-target exponential is non-coverable.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595GenericTargetLocal
open Erdos595Work

abbrev Shift := orderedShiftGraph ℕ
abbrev ShiftVertex := {p : ℕ × ℕ // p.1 < p.2}

lemma shift_no_finite_coloring (C : Type*) [Finite C] : IsEmpty (Shift.Coloring C) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨e⟩ := orderedShiftGraph_coloring_injection c
  haveI : Finite ℕ := Finite.of_injective e e.injective
  exact not_finite ℕ

noncomputable def coneEmbedding : coneGraph Shift ↪g Erdos595CountableExtension.G :=
  (Erdos595CountableGenericUniversality.universal_countable (coneGraph Shift)
    (coneGraph_cliqueFree Shift (orderedShiftGraph_cliqueFree ℕ))).some

/-- The neighborhood of this particular generic vertex has no finite proper palette. -/
theorem generic_neighborhood_unbounded :
    ∃ v : Erdos595CountableExtension.Vertex,
      ∀ n : ℕ, ¬(Erdos595CountableExtension.G.induce
        (Erdos595CountableExtension.G.neighborSet v)).Colorable n := by
  refine ⟨coneEmbedding none,?_⟩
  intro n hc
  obtain ⟨c⟩ := hc
  let j : Shift →g Erdos595CountableExtension.G.induce
      (Erdos595CountableExtension.G.neighborSet (coneEmbedding none)) :=
    { toFun := fun x => ⟨coneEmbedding (some x),coneEmbedding.map_rel_iff.mpr trivial⟩
      map_rel' := fun h => coneEmbedding.map_rel_iff.mpr h }
  exact (shift_no_finite_coloring (Fin n)).false (c.comp j)

/-- Even an arbitrary-cardinality target is impossible under these local finite bounds. -/
theorem no_hom_locally_finitely_colorable {W : Type*} (K : SimpleGraph W)
    (hK : ∀ w, ∃ n, (K.induce (K.neighborSet w)).Colorable n) :
    ¬Nonempty (Erdos595CountableExtension.G →g K) := by
  rintro ⟨f⟩
  let e := f.comp coneEmbedding.toHom
  obtain ⟨n,⟨c⟩⟩ := hK (e none)
  let j : Shift →g K.induce (K.neighborSet (e none)) :=
    { toFun := fun x => ⟨e (some x),e.map_adj trivial⟩
      map_rel' := fun h => e.map_adj h }
  exact (shift_no_finite_coloring (Fin n)).false (c.comp j)

theorem no_hom_locally_finite_target :
    ¬Nonempty (Erdos595CountableExtension.G →g Erdos595LocallyFiniteFolkmanTarget.H) := by
  apply no_hom_locally_finitely_colorable
  intro w
  exact ⟨Fintype.card (Erdos595LocallyFiniteFolkmanTarget.H.neighborSet w),
    SimpleGraph.colorable_of_fintype _⟩

#print axioms shift_no_finite_coloring
#print axioms generic_neighborhood_unbounded
#print axioms no_hom_locally_finitely_colorable
#print axioms no_hom_locally_finite_target
end Erdos595GenericTargetLocal
