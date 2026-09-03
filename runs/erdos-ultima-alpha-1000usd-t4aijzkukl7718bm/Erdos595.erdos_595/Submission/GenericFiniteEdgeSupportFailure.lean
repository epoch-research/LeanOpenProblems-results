import Submission.ThirdTriangleFiniteEdgeSupportFailure
import Submission.GenericUltrafilterUniversality

/-!
The same finite-edge-support failure occurs in the third mutual tower over
the fixed explicit countable generic base. This is not a non-coverability
conclusion for that tower.
-/

open SimpleGraph Set
open Erdos595FiniteEdgeCoverIdeal Erdos595GenericUltrafilterUniversality
namespace Erdos595GenericFiniteEdgeSupportFailure

lemma finiteOn_preimage {A B : Type} {H : SimpleGraph A} {K : SimpleGraph B}
    (f : H ↪g K) (S : Set B) (hS : FiniteOn K S) : FiniteOn H (f ⁻¹' S) := by
  obtain ⟨C,hC,hc⟩ := hS
  let g : H.induce (f ⁻¹' S) →g K.induce S :=
    ⟨fun x => ⟨f x.val,x.property⟩,fun h => f.map_rel_iff.mpr h⟩
  exact ⟨C,hC,hc.comap g⟩

open Erdos595CountableExtension
open Erdos595ThirdTriangleFiniteEdgeSupportFailure

theorem generic_third_triangle_with_no_finite_support :
    ∃ p q r : Carrier Vertex 3,
      (tower G G_cliqueFree 3).val.Adj p q ∧
      (tower G G_cliqueFree 3).val.Adj p r ∧
      (tower G G_cliqueFree 3).val.Adj q r ∧
      ∀ S, FiniteOn G S → p ∉ support S 3 := by
  obtain ⟨f⟩ := Erdos595CountableGenericUniversality.universal_countable K K_cliqueFree
  let e := towerEmbedding K_cliqueFree G_cliqueFree f 3
  refine ⟨e P,e (pure Q₀),e (pure Q₁),e.map_rel_iff.mpr third_triangle.1,
    e.map_rel_iff.mpr third_triangle.2.1,e.map_rel_iff.mpr third_triangle.2.2,?_⟩
  intro S hS hm
  have hp := (support_map_iff K_cliqueFree G_cliqueFree f S 3 P).mp hm
  exact no_finite_edge_support (f ⁻¹' S) (finiteOn_preimage f S hS) hp

#print axioms generic_third_triangle_with_no_finite_support
end Erdos595GenericFiniteEdgeSupportFailure
