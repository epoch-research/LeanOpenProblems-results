import Submission.EdgeHullPotential

/-! Structural facts about the terminal class of the adjacent-compression
reduction. These lemmas do not establish either compression or a linear
cycle-and-edge bound. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.Compression
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 400000

/-- Closed neighborhoods, as finite sets. -/
noncomputable def closedNeighbors (G : SimpleGraph V) (v : V) : Finset V :=
  insert v (G.neighborFinset v)

@[simp] lemma mem_closedNeighbors {v w : V} :
    w ∈ closedNeighbors G v ↔ w = v ∨ G.Adj v w := by
  simp [closedNeighbors]

lemma card_closedNeighbors (v : V) :
    (closedNeighbors G v).card = Nat.card (G.neighborSet v) + 1 := by
  rw [closedNeighbors, Finset.card_insert_of_notMem (by simp),
    SimpleGraph.card_neighborFinset_eq_degree]
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]

lemma NestedAlongEdges.closed_subset (hG : NestedAlongEdges G) {u v : V}
    (huv : G.Adj u v)
    (hd : Nat.card (G.neighborSet v) ≤ Nat.card (G.neighborSet u)) :
    closedNeighbors G v ⊆ closedNeighbors G u := by
  intro w hw
  rcases mem_closedNeighbors.mp hw with rfl | hvw
  · exact mem_closedNeighbors.mpr (Or.inr huv)
  · by_cases hwu : w = u
    · exact mem_closedNeighbors.mpr (Or.inl hwu)
    · exact mem_closedNeighbors.mpr (Or.inr (hG u v huv hd w hwu hvw))

/-- A degree-free characterization: closed neighborhoods of adjacent vertices
are comparable by inclusion. -/
lemma nestedAlongEdges_iff_closed_comparable :
    NestedAlongEdges G ↔ ∀ u v : V, G.Adj u v →
      closedNeighbors G u ⊆ closedNeighbors G v ∨
        closedNeighbors G v ⊆ closedNeighbors G u := by
  constructor
  · intro hG u v huv
    rcases le_total (Nat.card (G.neighborSet u)) (Nat.card (G.neighborSet v)) with h | h
    · exact Or.inl (hG.closed_subset huv.symm h)
    · exact Or.inr (hG.closed_subset huv h)
  · intro hG u v huv hd w hwu hvw
    have hvu : closedNeighbors G v ⊆ closedNeighbors G u := by
      rcases hG u v huv with h | h
      · have hc : (closedNeighbors G v).card ≤ (closedNeighbors G u).card := by
          simpa only [card_closedNeighbors, Nat.add_le_add_iff_right] using hd
        exact (Finset.eq_of_subset_of_card_le h hc).symm.le
      · exact h
    rcases mem_closedNeighbors.mp (hvu (mem_closedNeighbors.mpr (Or.inr hvw))) with h | h
    · exact (hwu h).elim
    · exact h

/-- Induced subgraphs inherit nested adjacent neighborhoods. Degree comparisons
in the induced graph need not agree with those in the original graph; the
closed-neighborhood characterization avoids that issue. -/
lemma NestedAlongEdges.induce (hG : NestedAlongEdges G) (S : Set V) :
    NestedAlongEdges (G.induce S) := by
  apply nestedAlongEdges_iff_closed_comparable.mpr
  intro u v huv
  have h := nestedAlongEdges_iff_closed_comparable.mp hG u.val v.val huv
  have lift : ∀ a b : S, closedNeighbors G a.val ⊆ closedNeighbors G b.val →
      closedNeighbors (G.induce S) a ⊆ closedNeighbors (G.induce S) b := by
    intro a b hab w hw
    have hw' : w.val ∈ closedNeighbors G a.val := by
      rcases mem_closedNeighbors.mp hw with rfl | h
      · exact mem_closedNeighbors.mpr (Or.inl rfl)
      · exact mem_closedNeighbors.mpr (Or.inr h)
    rcases mem_closedNeighbors.mp (hab hw') with h | h
    · exact mem_closedNeighbors.mpr (Or.inl (Subtype.ext h))
    · exact mem_closedNeighbors.mpr (Or.inr h)
  exact h.imp (lift u v) (lift v u)

/-- Every connected induced subgraph of a terminal graph has a universal
vertex. This is the recursive structure required by a terminal argument. -/
lemma NestedAlongEdges.induce_exists_universal (hG : NestedAlongEdges G)
    (S : Set V) (hc : (G.induce S).Connected) :
    ∃ u : S, ∀ v : S, v ≠ u → G.Adj u.val v.val := by
  exact (hG.induce S).exists_universal hc

/-- An edge cannot have private neighbors at both endpoints. This excludes
both possible induced four-vertex configurations (a path or a four-cycle). -/
lemma NestedAlongEdges.no_two_private_neighbors (hG : NestedAlongEdges G)
    {u v w x : V} (huv : G.Adj u v)
    (huw : G.Adj u w) (hvw : ¬ G.Adj v w) (hwv : w ≠ v)
    (hvx : G.Adj v x) (hux : ¬ G.Adj u x) (hxu : x ≠ u) : False := by
  rcases le_total (Nat.card (G.neighborSet u)) (Nat.card (G.neighborSet v)) with h | h
  · exact hvw (hG v u huv.symm h w hwv huw)
  · exact hux (hG u v huv h x hxu hvx)

#print axioms nestedAlongEdges_iff_closed_comparable
#print axioms NestedAlongEdges.induce
#print axioms NestedAlongEdges.induce_exists_universal
end Erdos184Work.Compression
