import Submission.FiniteEdgeSupportTowerCover

/-! A direct corollary of the existing support example: countable
coverability at every finite mutual-ultrafilter stage does not reflect to
finite coverability of the countable base. This does not settle Erdős 595. -/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595FiniteTowerReflectionFailure
open Erdos595Work Erdos595FinitePalette Erdos595GenericUltrafilterUniversality
open Erdos595FiniteEdgeSupportFailure Erdos595ThirdTriangleFiniteEdgeSupportFailure

/-- The base of the previously constructed tower has no finite edge palette. -/
theorem base_no_finite (C : Type) [Finite C] : ¬HasColoring K C := by
  intro hc
  let f : G.induce (univ : Set Vertex) →g K :=
    Erdos595ThirdTriangleFiniteEdgeSupportFailure.oldEmbedding.toHom.comp
      (SimpleGraph.Embedding.induce (univ : Set Vertex)).toHom
  exact no_common_finite_support univ (fun _ => Filter.univ_mem) C (hc.comap f)

/-- In particular no unrestricted countable-to-finite reflection theorem
can hold at any fixed finite stage, or even at all finite stages together. -/
theorem reflection_failure :
    ∃ (V : Type) (_ : Countable V) (_ : Infinite V)
      (G : SimpleGraph V) (hG : G.CliqueFree 4),
      (∀ n, IsCountableUnionOfTriangleFree (tower G hG n).val) ∧
      (∀ (C : Type) (_ : Finite C), ¬HasColoring G C) := by
  exact ⟨NewVertex,inferInstance,inferInstance,K,K_cliqueFree,
    Erdos595FiniteEdgeSupportTowerCover.every_finite_tower_cover,fun C _ => base_no_finite C⟩

#print axioms base_no_finite
#print axioms reflection_failure
end Erdos595FiniteTowerReflectionFailure
