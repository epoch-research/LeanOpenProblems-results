import Submission.SecondArcReflection
import Submission.SecondArcTransversal
import Submission.SecondArcTriangleStructure

/-!
An exact reduction of the universal covering problem to second right
adjoints of graphs having an independent triangle transversal. This is a
reduction of Erdős 595, not a proof of either answer.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595SecondArcNormalForm
open Erdos595ArcAdjoint Erdos595Work
universe u

/-- Removing the independent set leaves no triangle. -/
def IndependentTriangleTransversal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ S : Set V, (G.induce Sᶜ).CliqueFree 3 ∧
    ∀ a ∈ S, ∀ b ∈ S, ¬G.Adj a b

lemma second_arc_transversal {V : Type*} (G : SimpleGraph V) :
    IndependentTriangleTransversal (arcGraph (arcGraph G)) := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  refine ⟨{p | Erdos595SecondArcTransversal.Selected G p},
    Erdos595SecondArcTransversal.base_triangleFree G,?_⟩
  intro p hp q hq
  exact Erdos595SecondArcTransversal.independent G hp hq

/-- The special class is sufficient to decide the full universal statement.
The second-right K4 condition is on the FULL target, not a selected subgraph. -/
theorem universal_cover_iff :
    (∀ (V : Type u) (G : SimpleGraph V), G.CliqueFree 4 →
      IsCountableUnionOfTriangleFree G) ↔
    (∀ (V : Type u) (H : SimpleGraph V), IndependentTriangleTransversal H →
      (right (right H)).CliqueFree 4 → IsCountableUnionOfTriangleFree (right (right H))) := by
  refine ⟨fun h V H _ hH => h _ _ hH,?_⟩
  intro h V G hG
  apply Erdos595SecondArcReflection.source_cover_of_twice_cover G
  exact h _ _ (second_arc_transversal G)
    ((Erdos595SecondArcReflection.right_twice_arc_twice_cliqueFree_iff G).mpr hG)

/-- In particular any genuine non-coverable K4-free graph gives a genuine
non-coverable second-right graph in the independent-transversal class. -/
theorem witness_normal_form :
    (∃ (V : Type u) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ¬IsCountableUnionOfTriangleFree G) ↔
    (∃ (V : Type u) (H : SimpleGraph V), IndependentTriangleTransversal H ∧
      (right (right H)).CliqueFree 4 ∧
      ¬IsCountableUnionOfTriangleFree (right (right H))) := by
  constructor
  · rintro ⟨V,G,hG,hn⟩
    exact ⟨_,arcGraph (arcGraph G),second_arc_transversal G,
      (Erdos595SecondArcReflection.right_twice_arc_twice_cliqueFree_iff G).mpr hG,
      fun hc => hn (Erdos595SecondArcReflection.source_cover_of_twice_cover G hc)⟩
  · rintro ⟨V,H,_,hH,hn⟩
    exact ⟨_,right (right H),hH,hn⟩

#print axioms second_arc_transversal
#print axioms universal_cover_iff
#print axioms witness_normal_form
/-- A still more restricted exact base class: its triangles are disjoint,
and one can select an independent set meeting all of them. -/
def SparseTriangleBase {V : Type*} (H : SimpleGraph V) : Prop :=
  IndependentTriangleTransversal H ∧
    Erdos595SecondArcTriangleStructure.VertexDisjointTriangles H

lemma second_arc_sparse {V : Type*} (G : SimpleGraph V) :
    SparseTriangleBase (arcGraph (arcGraph G)) :=
  ⟨second_arc_transversal G,
    Erdos595SecondArcTriangleStructure.second_arc_vertex_disjoint G⟩

theorem universal_cover_sparse_iff :
    (∀ (V : Type u) (G : SimpleGraph V), G.CliqueFree 4 →
      IsCountableUnionOfTriangleFree G) ↔
    (∀ (V : Type u) (H : SimpleGraph V), SparseTriangleBase H →
      (right (right H)).CliqueFree 4 → IsCountableUnionOfTriangleFree (right (right H))) := by
  refine ⟨fun h V H _ hH => h _ _ hH,?_⟩
  intro h V G hG
  apply Erdos595SecondArcReflection.source_cover_of_twice_cover G
  exact h _ _ (second_arc_sparse G)
    ((Erdos595SecondArcReflection.right_twice_arc_twice_cliqueFree_iff G).mpr hG)

theorem witness_sparse_normal_form :
    (∃ (V : Type u) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ¬IsCountableUnionOfTriangleFree G) ↔
    (∃ (V : Type u) (H : SimpleGraph V), SparseTriangleBase H ∧
      (right (right H)).CliqueFree 4 ∧
      ¬IsCountableUnionOfTriangleFree (right (right H))) := by
  constructor
  · rintro ⟨V,G,hG,hn⟩
    exact ⟨_,arcGraph (arcGraph G),second_arc_sparse G,
      (Erdos595SecondArcReflection.right_twice_arc_twice_cliqueFree_iff G).mpr hG,
      fun hc => hn (Erdos595SecondArcReflection.source_cover_of_twice_cover G hc)⟩
  · rintro ⟨V,H,_,hH,hn⟩
    exact ⟨_,right (right H),hH,hn⟩

#print axioms universal_cover_sparse_iff
#print axioms witness_sparse_normal_form

end Erdos595SecondArcNormalForm
