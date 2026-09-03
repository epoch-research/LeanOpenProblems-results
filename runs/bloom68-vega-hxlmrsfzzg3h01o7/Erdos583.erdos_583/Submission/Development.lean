import FormalConjecturesUtil

/-!
Scratch formalization of the indexed-family interface for Erdős 583.
The two definitions below are copied verbatim from Spec.lean. This file does
not import or use either of the conjecture placeholders.
-/

open SimpleGraph

namespace Erdos583Development

/-- The same predicate as `Erdos583.IsPathSubgraph`. -/
def IsPathSubgraph {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ H = p.toSubgraph

/-- The same predicate as `Erdos583.IsDecomposition`. -/
def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

/-- Convert a finite indexed simple-path edge partition to the exact Finset interface. -/
theorem of_indexed_paths {V I : Type*} {G : SimpleGraph V} [Fintype I]
    (u v : I → V) (p : (i : I) → G.Walk (u i) (v i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (p i).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsPathSubgraph H) ∧ IsDecomposition G D ∧
        D.card ≤ Fintype.card I := by
  classical
  let f : I → G.Subgraph := fun i => (p i).toSubgraph
  let D : Finset G.Subgraph := Finset.univ.image f
  refine ⟨D, ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    exact ⟨u i, v i, p i, hp i, rfl⟩
  · constructor
    · intro H hH K hK hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hK
      have hij : i ≠ j := fun hij => hne (congrArg f hij)
      change Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet
      simpa only [Walk.edgeSet_toSubgraph, Walk.edgeSet] using hd hij
    · ext e
      constructor
      · intro he
        obtain ⟨H, he⟩ := Set.mem_iUnion.mp he
        obtain ⟨hH, he⟩ := Set.mem_iUnion.mp he
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
        exact (p i).edges_subset_edgeSet ((p i).mem_edges_toSubgraph.mp he)
      · intro he
        obtain ⟨i, hi⟩ := hc e he
        apply Set.mem_iUnion.mpr
        refine ⟨f i, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        · exact (p i).mem_edges_toSubgraph.mpr hi
  · exact (Finset.card_image_le).trans_eq (Finset.card_univ)

#print axioms of_indexed_paths

end Erdos583Development
