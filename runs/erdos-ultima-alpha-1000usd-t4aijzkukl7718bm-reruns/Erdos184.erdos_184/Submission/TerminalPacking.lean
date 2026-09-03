import Submission.MarkedCyclePaths

/-!
A small API for exact cycle packings on specified edge sets. It is used for
terminal routing operations, not as an unconditional decomposition bound.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TerminalRouting
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Packing (G : SimpleGraph V) where
  pieces : Finset G.Subgraph
  cycles : ∀ H ∈ pieces, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2
  disjoint : Set.PairwiseDisjoint (pieces : Set G.Subgraph) (fun H => H.edgeSet)

noncomputable def Packing.edges (P : Packing G) : Set (Sym2 V) := ⋃ H ∈ P.pieces, H.edgeSet

def walkEdges {a b : V} (p : G.Walk a b) : Set (Sym2 V) := {e | e ∈ p.edges}
def walkVerts {a b : V} (p : G.Walk a b) : Set V := {x | x ∈ p.support}

omit [Fintype V] in
@[simp] lemma mem_walkEdges {a b : V} (p : G.Walk a b) (e : Sym2 V) :
    e ∈ walkEdges p ↔ e ∈ p.edges := Iff.rfl
omit [Fintype V] in
@[simp] lemma mem_walkVerts {a b : V} (p : G.Walk a b) (x : V) :
    x ∈ walkVerts p ↔ x ∈ p.support := Iff.rfl
omit [Fintype V] in
@[simp] lemma walkEdges_reverse {a b : V} (p : G.Walk a b) :
    walkEdges p.reverse = walkEdges p := by ext e; simp [walkEdges]
omit [Fintype V] in
@[simp] lemma walkVerts_reverse {a b : V} (p : G.Walk a b) :
    walkVerts p.reverse = walkVerts p := by ext x; simp [walkVerts]

lemma Packing.piece_edges_subset (P : Packing G) {H : G.Subgraph} (hH : H ∈ P.pieces) :
    H.edgeSet ⊆ P.edges := fun _ he => Set.mem_iUnion₂.mpr ⟨H,hH,he⟩

noncomputable def Packing.union (P Q : Packing G) (h : Disjoint P.edges Q.edges) : Packing G where
  pieces := P.pieces ∪ Q.pieces
  cycles H hH := by
    rcases Finset.mem_union.mp hH with hH | hH
    · exact P.cycles H hH
    · exact Q.cycles H hH
  disjoint := by
    intro H hH K hK hne
    rcases Finset.mem_union.mp hH with hH | hH <;>
      rcases Finset.mem_union.mp hK with hK | hK
    · exact P.disjoint hH hK hne
    · exact h.mono (P.piece_edges_subset hH) (Q.piece_edges_subset hK)
    · exact h.symm.mono (Q.piece_edges_subset hH) (P.piece_edges_subset hK)
    · exact Q.disjoint hH hK hne

lemma Packing.union_edges (P Q : Packing G) (h : Disjoint P.edges Q.edges) :
    (P.union Q h).edges = P.edges ∪ Q.edges := by
  ext e
  simp only [Packing.edges,Packing.union,Finset.mem_union,Set.mem_iUnion,Set.mem_union]
  aesop

lemma Packing.union_card_le (P Q : Packing G) (h : Disjoint P.edges Q.edges) :
    (P.union Q h).pieces.card ≤ P.pieces.card + Q.pieces.card := Finset.card_union_le _ _

lemma packing_of_cycle {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    ∃ P : Packing G, P.edges = walkEdges p ∧ P.pieces.card ≤ 1 := by
  let P : Packing G := ⟨{p.toSubgraph},by
    intro H hH
    obtain rfl := Finset.mem_singleton.mp hH
    exact cycle_subgraph_regular G hp,by simp⟩
  refine ⟨P,?_,by simp [P]⟩
  ext e
  simp only [Packing.edges,P,Finset.mem_singleton,Set.iUnion_iUnion_eq_left,
    Walk.mem_edges_toSubgraph,mem_walkEdges]

/-- One paired path from each side has rank cost at most |S|-1. -/
lemma packing_of_two_paths {a b : V} (p : G.Walk a b) (q : G.Walk b a)
    (hp : p.IsPath) (hq : q.IsPath) (hd : Disjoint (walkEdges p) (walkEdges q))
    (S : Set V) (hi : walkVerts p ∩ walkVerts q ⊆ S) :
    ∃ P : Packing G, P.edges = walkEdges p ∪ walkEdges q ∧ P.pieces.card+1 ≤ S.ncard := by
  obtain ⟨D,hc,hdis,hcov,hcard⟩ := PathUnionRank.paths_to_packing_of_inter_subset p q hp hq
    (Set.disjoint_left.mp hd) S (by simpa only [Walk.verts_toSubgraph] using hi)
  exact ⟨⟨D,hc,hdis⟩,Set.ext hcov,hcard⟩

/-- Two pairings that agree are glued independently. Other intersections
within a side are allowed; only intersections across sides are charged. -/
lemma packing_of_compatible_paths {a b c d : V}
    (p : G.Walk a b) (q : G.Walk c d) (r : G.Walk b a) (s : G.Walk d c)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) (hs : s.IsPath)
    (hpq : Disjoint (walkEdges p) (walkEdges q))
    (hrs : Disjoint (walkEdges r) (walkEdges s))
    (hcross : Disjoint (walkEdges p ∪ walkEdges q) (walkEdges r ∪ walkEdges s))
    (S : Set V) (hi : (walkVerts p ∪ walkVerts q) ∩ (walkVerts r ∪ walkVerts s) ⊆ S) :
    ∃ P : Packing G,
      P.edges = (walkEdges p ∪ walkEdges q) ∪ (walkEdges r ∪ walkEdges s) ∧
      P.pieces.card + 2 ≤ 2*S.ncard := by
  obtain ⟨P,hP,hbP⟩ := packing_of_two_paths p r hp hr
    (hcross.mono Set.subset_union_left Set.subset_union_left) S
    (fun _ h => hi ⟨Or.inl h.1,Or.inl h.2⟩)
  obtain ⟨Q,hQ,hbQ⟩ := packing_of_two_paths q s hq hs
    (hcross.mono Set.subset_union_right Set.subset_union_right) S
    (fun _ h => hi ⟨Or.inr h.1,Or.inr h.2⟩)
  have hPQ : Disjoint P.edges Q.edges := by
    rw [hP,hQ]
    apply Set.disjoint_left.mpr
    intro e he hf
    rcases he with he | he <;> rcases hf with hf | hf
    · exact Set.disjoint_left.mp hpq he hf
    · exact Set.disjoint_left.mp hcross (Or.inl he) (Or.inr hf)
    · exact Set.disjoint_left.mp hcross (Or.inr hf) (Or.inl he)
    · exact Set.disjoint_left.mp hrs he hf
  refine ⟨P.union Q hPQ,?_,?_⟩
  · rw [Packing.union_edges,hP,hQ]
    ext e
    simp only [Set.mem_union]
    tauto
  · have hh := P.union_card_le Q hPQ
    omega

end Erdos184.TerminalRouting
