import Submission.DelayedUltrafilter

/-!
One-sided trace cones give triangle-free supports at the third mutual
ultrafilter stage. The cones are indexed by ultrafilters, not by subsets of
the original carrier. No countable-cover conclusion is asserted.
-/

set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595OneSidedSupport
open Erdos595Work Erdos595DelayedUltrafilter

variable {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4)

abbrev G₁ := ultrafilterGraph G hG
abbrev G₂ := ultrafilterGraph (G₁ G hG) (ultrafilterGraph_cliqueFree G hG)
abbrev G₃ := ultrafilterGraph (G₂ G hG)
  (ultrafilterGraph_cliqueFree (G₁ G hG) (ultrafilterGraph_cliqueFree G hG))

/-- The one-sided out-neighborhood of an original ultrafilter. -/
def cone (r : Ultrafilter V) : Set (Ultrafilter V) := {p | fubiniAdj G r p}

/-- A directed transitive four-clique would contradict the base clique bound. -/
theorem cone_triangleFree (r : Ultrafilter V) :
    ((G₁ G hG).induce (cone G r)).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨p,q,t,hpq,hpt,hqt,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact no_four_fubini G hG r p q t p.property q.property t.property
    hpq.1 hpt.1 hqt.1

/-- A second-stage neighborhood trace lies in the cone of its flattened
ultrafilter. This implication does not make flattening a homomorphism. -/
theorem trace_subset_cone (Q : Ultrafilter (Ultrafilter V)) :
    {p | (G₁ G hG).neighborSet p ∈ Q} ⊆ cone G (flatten Q) := by
  intro p hp
  change {v | G.neighborSet v ∈ p} ∈ flatten Q
  rw [mem_flatten]
  apply Filter.mem_of_superset hp
  intro q hq
  exact hq.2

/-- One cone support for an adjacent second-stage vertex, with its index
explicitly the flattening of the other endpoint. -/
theorem second_supported (P Q : Ultrafilter (Ultrafilter V))
    (hPQ : (G₂ G hG).Adj P Q) : cone G (flatten Q) ∈ P := by
  apply Filter.mem_of_superset hPQ.1
  exact trace_subset_cone G hG Q

/-- At stage three, any nonisolated vertex is supported on two lifts of a
single triangle-free cone of first-stage vertices. -/
theorem third_supported
    (X Y : Ultrafilter (Ultrafilter (Ultrafilter V)))
    (hXY : (G₃ G hG).Adj X Y) :
    ∃ r : Ultrafilter V, {P | cone G r ∈ P} ∈ X := by
  obtain ⟨Q,hQ⟩ := Ultrafilter.nonempty_of_mem hXY.2
  refine ⟨flatten Q,Filter.mem_of_superset hQ ?_⟩
  intro P hP
  exact second_supported G hG P Q hP.symm

/-- The cone index may be chosen with triangle-free original support,
because it is the flattening of a nonisolated second-stage point. This does
not bound the number of possible indices by the number of original subsets. -/
theorem third_supported_refined
    (X Y : Ultrafilter (Ultrafilter (Ultrafilter V)))
    (hXY : (G₃ G hG).Adj X Y) :
    ∃ (r : Ultrafilter V) (S : Set V),
      (G.induce S).CliqueFree 3 ∧ S ∈ r ∧ {P | cone G r ∈ P} ∈ X := by
  obtain ⟨Q,hQ⟩ := Ultrafilter.nonempty_of_mem hXY.2
  obtain ⟨P,hQP⟩ := Ultrafilter.nonempty_of_mem hQ
  obtain ⟨S,hS,hSQ⟩ := second_ultrafilter_support G hG Q P hQP
  refine ⟨flatten Q,S,hS,(mem_flatten Q S).mpr hSQ,?_⟩
  apply Filter.mem_of_superset hQ
  intro P hP
  exact second_supported G hG P Q hP.symm

/-- The actual double support of a cone remains triangle-free at stage three. -/
theorem third_support_triangleFree (r : Ultrafilter V) :
    ((G₃ G hG).induce {X | {P | cone G r ∈ P} ∈ X}).CliqueFree 3 := by
  have h₁ := cone_triangleFree G hG r
  have h₂ := ultrafilterGraph_support_cliqueFree (G₁ G hG)
    (ultrafilterGraph_cliqueFree G hG) (cone G r) h₁
  exact ultrafilterGraph_support_cliqueFree (G₂ G hG)
    (ultrafilterGraph_cliqueFree (G₁ G hG) (ultrafilterGraph_cliqueFree G hG))
    {P | cone G r ∈ P} h₂

#print axioms cone_triangleFree
#print axioms trace_subset_cone
#print axioms second_supported
#print axioms third_supported
#print axioms third_supported_refined
#print axioms third_support_triangleFree
end Erdos595OneSidedSupport
