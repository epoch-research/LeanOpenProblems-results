import Submission.DominatedMarkedSecondRight

/-!
Independent apex families over a triangle-free base, with dominating-edge
(or complete-bipartite) neighborhoods, have two-piece-covered full second
right adjoints. Arbitrarily large star neighborhoods are included.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595BipartiteNeighborhoodApex
open Erdos595ArcAdjoint Erdos595DominatedMarkedSecondRight
variable {V E : Type*} (B : SimpleGraph V) (N : E → Set V)

def graph : SimpleGraph (V ⊕ E) where
  Adj
    | .inl a, .inl b => B.Adj a b
    | .inl a, .inr e => a ∈ N e
    | .inr e, .inl a => a ∈ N e
    | .inr _, .inr _ => False
  symm := by
    intro a b
    cases a <;> cases b
    · exact SimpleGraph.Adj.symm
    · exact id
    · exact id
    · exact id
  loopless := by
    intro a
    cases a
    · exact B.loopless _
    · exact id

def mark : V ⊕ E → Bool
  | .inl _ => false
  | .inr _ => true

variable (hB : B.CliqueFree 3)

include hB in
theorem mark_exact :
    Erdos595ExactTransversalRight.ExactTransversal (graph B N) mark := by
  classical
  intro a b c hab hac hbc
  cases a <;> cases b <;> cases c <;>
    simp_all only [graph,mark,Bool.toNat_false,Bool.toNat_true,Nat.zero_add,Nat.add_zero]
  exact (hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)).elim

/-- A local condition on each allowed apex neighborhood. -/
def DominatingEdges : Prop :=
  ∀ e a b d, a ∈ N e → b ∈ N e → d ∈ N e → B.Adj a b →
    B.Adj a d ∨ B.Adj b d

theorem mark_dominated (hN : DominatingEdges B N) : Dominated (graph B N) mark := by
  intro a b c ha hab hac hbc d had
  cases a with
  | inl a => cases ha
  | inr e =>
    cases b with
    | inr b => exact hab.elim
    | inl b =>
      cases c with
      | inr c => exact hac.elim
      | inl c =>
        cases d with
        | inr d => exact had.elim
        | inl d => exact hN e b c d hab hac had hbc

include hB in
theorem second_right_two_cover (hN : DominatingEdges B N) :
    Erdos595CompleteFilterEdgeCover.CoversWith (right (right (graph B N))) 2 :=
  Erdos595DominatedMarkedSecondRight.second_right_two_cover (graph B N) mark
    (mark_exact B N hB) (mark_dominated B N hN)

include hB in
theorem second_right_cover (hN : DominatingEdges B N) :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (right (graph B N))) :=
  (show Erdos595BadEdge.FiniteCover (right (right (graph B N))) from
    ⟨2,second_right_two_cover B N hB hN⟩).countable

/-- Complete bipartite neighborhoods satisfy the local condition. Empty
parts and empty neighborhoods are allowed. -/
theorem dominating_of_complete_bipartite (c : E → V → Bool)
    (hc : ∀ e a b, a ∈ N e → b ∈ N e → (B.Adj a b ↔ c e a ≠ c e b)) :
    DominatingEdges B N := by
  intro e a b d ha hb hd hab
  have hne := (hc e a b ha hb).mp hab
  by_cases he : c e a = c e d
  · exact Or.inr ((hc e b d hb hd).mpr (fun h => hne (he.trans h.symm)))
  · exact Or.inl ((hc e a d ha hd).mpr he
    )

include hB in
theorem two_cover_of_complete_bipartite (c : E → V → Bool)
    (hc : ∀ e a b, a ∈ N e → b ∈ N e → (B.Adj a b ↔ c e a ≠ c e b)) :
    Erdos595CompleteFilterEdgeCover.CoversWith (right (right (graph B N))) 2 :=
  second_right_two_cover B N hB (dominating_of_complete_bipartite B N c hc)

include hB in
/-- Any subset of a closed neighborhood in a triangle-free base is an
allowable star neighborhood. There is no degree or cardinality bound. -/
theorem dominating_of_stars (center : E → V)
    (hN : ∀ e a, a ∈ N e → a = center e ∨ B.Adj (center e) a) :
    DominatingEdges B N := by
  classical
  intro e a b d ha hb hd hab
  rcases hN e a ha with rfl | hca
  · rcases hN e d hd with rfl | hcd
    · exact Or.inr hab.symm
    · exact Or.inl hcd
  · rcases hN e b hb with rfl | hcb
    · rcases hN e d hd with rfl | hcd
      · exact Or.inl hab
      · exact Or.inr hcd
    · exact (hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hca,hcb,hab⟩)).elim

include hB in
theorem two_cover_of_stars (center : E → V)
    (hN : ∀ e a, a ∈ N e → a = center e ∨ B.Adj (center e) a) :
    Erdos595CompleteFilterEdgeCover.CoversWith (right (right (graph B N))) 2 :=
  second_right_two_cover B N hB (dominating_of_stars B N hB center hN)

#print axioms second_right_two_cover
#print axioms two_cover_of_complete_bipartite
#print axioms two_cover_of_stars
end Erdos595BipartiteNeighborhoodApex
