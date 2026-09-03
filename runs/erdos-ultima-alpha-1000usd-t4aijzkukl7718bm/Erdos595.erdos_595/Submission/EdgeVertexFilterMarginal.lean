import Submission.TriangleFilterCoupling
import Submission.VertexCoverFilter

/-!
The endpoint marginal of the canonical avoiding edge filter is exactly the
vertex-cover filter. Thus endpoint marginals have continuum-successor
completeness. This is NOT a completeness upgrade of the whole edge filter,
and does not settle Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595EdgeVertexMarginal
open Erdos595Work Erdos595CountableBadEdge Erdos595VertexCoverFilter

variable {V : Type} (G : SimpleGraph V)

abbrev Edge := Erdos595ArcAdjoint.Arc G

/-- The canonical edge and vertex ideals give exactly matching marginals. -/
theorem map_fst :
    Filter.map (fun e : Edge G => e.val.1) (coveringFilter G) = vertexFilter G := by
  classical
  apply Filter.ext
  intro S
  constructor
  · intro hS
    change {e : Edge G | e.val.1 ∈ S} ∈ coveringFilter G at hS
    obtain ⟨T,hT,hTc,hsub⟩ := Filter.mem_countableGenerate_iff.mp hS
    letI : Countable T := hTc.to_subtype
    choose H hH hEq using fun t : T => hT t.property
    change IsCountableUnionOfTriangleFree (span G Sᶜ)
    apply cover_of_countable_family (span G Sᶜ) H hH
    intro a b hab
    by_contra hn
    push_neg at hn
    have he : (⟨(a,b),hab.1⟩ : Edge G) ∈ ⋂₀ T := by
      intro s hs
      have hh := hEq ⟨s,hs⟩
      change s = _ at hh
      rw [hh]
      exact hn ⟨s,hs⟩
    exact hab.2.1 (hsub he)
  · intro hS
    change On G Sᶜ at hS
    have hn := avoids_coverable G (coveringFilter G) (coveringFilter_avoids G)
      (span G Sᶜ) hS
    have he := endpoint_agreement G (coveringFilter G) (coveringFilter_avoids G) S
    change {e : Edge G | e.val.1 ∈ S} ∈ coveringFilter G
    filter_upwards [hn,he] with e hn he
    by_contra hnot
    exact hn ⟨e.property,hnot,fun h => hnot (he.mpr h)⟩

theorem map_snd :
    Filter.map (fun e : Edge G => e.val.2) (coveringFilter G) = vertexFilter G :=
  (marginals_equal G (coveringFilter G) (coveringFilter_avoids G)).symm.trans (map_fst G)

/-- Only the endpoint marginal is asserted to have this stronger completeness. -/
theorem endpoint_cardinalInter :
    CardinalInterFilter (Filter.map (fun e : Edge G => e.val.1) (coveringFilter G))
      (Order.succ Cardinal.continuum) := by
  rw [map_fst]
  infer_instance

open Erdos595TriangleFilterCoupling

def vertex (i : Fin 3) (t : Triangle G) : V :=
  if i = 0 then t.a else if i = 1 then t.b else t.c

/-- All three vertex marginals of the triangle coupling equal the same
continuum-complete vertex filter. -/
theorem triangle_vertex (i : Fin 3) :
    Filter.map (vertex G i) (triangleFilter G) = vertexFilter G := by
  fin_cases i
  · have h := congrArg (Filter.map (fun e : Edge G => e.val.1)) (map_side G 0)
    rw [Filter.map_map] at h
    exact h.trans (map_fst G)
  · have h := congrArg (Filter.map (fun e : Edge G => e.val.2)) (map_side G 0)
    rw [Filter.map_map] at h
    exact h.trans (map_snd G)
  · have h := congrArg (Filter.map (fun e : Edge G => e.val.2)) (map_side G 1)
    rw [Filter.map_map] at h
    exact h.trans (map_snd G)

theorem triangle_vertex_cardinalInter (i : Fin 3) :
    CardinalInterFilter (Filter.map (vertex G i) (triangleFilter G))
      (Order.succ Cardinal.continuum) := by
  rw [triangle_vertex]
  infer_instance

/-- The original countable-neighborhood avoidance extends to a family of
size at most continuum, by passing through the endpoint marginals. -/
theorem avoids_neighborhoods {I : Type} (hG : G.CliqueFree 4)
    (hI : Cardinal.mk I ≤ Cardinal.continuum) (d : I → V) :
    ∀ᶠ e : Edge G in coveringFilter G, ∀ i,
      ¬G.Adj (d i) e.val.1 ∧ ¬G.Adj (d i) e.val.2 := by
  have h := avoids_neighborhood_family G hG hI d
  have hfst : ∀ᶠ e : Edge G in coveringFilter G, ∀ i, ¬G.Adj (d i) e.val.1 := by
    have hm := h
    rw [← map_fst G] at hm
    exact hm
  have hsnd : ∀ᶠ e : Edge G in coveringFilter G, ∀ i, ¬G.Adj (d i) e.val.2 := by
    have hm := h
    rw [← map_snd G] at hm
    exact hm
  filter_upwards [hfst,hsnd] with e hf hs
  exact fun i => ⟨hf i,hs i⟩

#print axioms map_fst
#print axioms endpoint_cardinalInter
#print axioms triangle_vertex
#print axioms avoids_neighborhoods
end Erdos595EdgeVertexMarginal
