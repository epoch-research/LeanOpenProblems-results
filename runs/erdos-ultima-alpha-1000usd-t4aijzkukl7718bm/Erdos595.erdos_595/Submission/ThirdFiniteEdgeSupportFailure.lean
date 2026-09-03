import Submission.FiniteEdgeSupportFailure
import Submission.FiniteEdgeCoverIdeal

/-!
A nonisolated third-stage point can have no original support admitting
any finite triangle-free edge palette. The base is countable and K4-free.
This is not a proof or disproof of Erdős 595.
-/

open SimpleGraph Set Filter
open Erdos595Work Erdos595FinitePalette Erdos595FiniteEdgeCoverIdeal
open Erdos595FiniteEdgeSupportFailure
namespace Erdos595ThirdFiniteEdgeSupportFailure

lemma exists_avoiding : ∃ U : Ultrafilter Label,
    ∀ S : Set Vertex, FiniteOn G S → {z | S ∉ point z} ∈ U := by
  apply avoiding_ultrafilter (FiniteOn G) (finiteOn_empty G)
    (fun S T hS hT => hS.union hT) point
  intro S hS
  by_contra! hn
  obtain ⟨C,hC,hc⟩ := hS
  letI := hC
  exact no_common_finite_support S hn C hc

noncomputable def U : Ultrafilter Label := exists_avoiding.choose

lemma U_avoids (S : Set Vertex) (hS : FiniteOn G S) : {z | S ∉ point z} ∈ U :=
  exists_avoiding.choose_spec S hS

abbrev G₂ := ultrafilterGraph G₁ (ultrafilterGraph_cliqueFree G G_cliqueFree)
abbrev G₃ := ultrafilterGraph G₂ (ultrafilterGraph_cliqueFree G₁ (ultrafilterGraph_cliqueFree G G_cliqueFree))

noncomputable def P : Ultrafilter (Ultrafilter (Ultrafilter Vertex)) :=
  Ultrafilter.map (fun z => (pure (point z) : Ultrafilter (Ultrafilter Vertex))) U

lemma third_edge : G₃.Adj P (pure Q) := by
  rw [adj_pure,P,Ultrafilter.mem_map]
  apply Filter.Eventually.of_forall
  intro z
  change G₂.Adj Q (pure (point z))
  rw [adj_pure]
  exact point_mem_trace z

def lift₃ (S : Set Vertex) : Set (Ultrafilter (Ultrafilter Vertex)) :=
  {R | {p | S ∈ p} ∈ R}

lemma mem_lift₃ (S : Set Vertex) : lift₃ S ∈ P ↔ {z | S ∈ point z} ∈ U := by
  rw [P,Ultrafilter.mem_map]
  rfl

/-- The finite-EDGE-cover support claim fails, not just the older
triangle-free-VERTEX-support claim. -/
theorem no_finite_edge_support (S : Set Vertex) (hS : FiniteOn G S) : lift₃ S ∉ P := by
  intro hm
  rw [mem_lift₃] at hm
  obtain ⟨z,hno,hy⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (U_avoids S hS) hm)
  exact hno hy

theorem concrete_failure :
    (∃ R, G₃.Adj P R) ∧
    ∀ (S : Set Vertex) (C : Type) (_ : Finite C),
      HasColoring (G.induce S) C → lift₃ S ∉ P := by
  refine ⟨⟨pure Q,third_edge⟩,?_⟩
  intro S C hC hc
  exact no_finite_edge_support S ⟨C,hC,hc⟩

example : Countable Vertex := inferInstance
#print axioms third_edge
#print axioms no_finite_edge_support
#print axioms concrete_failure
end Erdos595ThirdFiniteEdgeSupportFailure
