import Submission.RigidityDegree

/-! Exact cardinality of cycle partitions lifted from labelled path families.
The two-label constructor covers parallel paths without assuming an internal
vertex on either path. This is infrastructure, not a linear bound. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.PathSubstitution
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {V W J : Type*} {G : SimpleGraph V}

namespace Family
variable (F : Family J W G)

/-- A cycle in the host graph, with exact labels of its constituent paths. -/
structure Circuit where
  root : V
  walk : G.Walk root root
  isCycle : walk.IsCycle
  labels : Finset J
  edges : ∀ e, e ∈ walk.edges ↔ ∃ j ∈ labels, e ∈ (F.path j).edges

namespace Circuit

noncomputable def ofModel (H : SimpleGraph W) (r : H.Dart → J)
    (he : ∀ d, s(F.src (r d),F.dst (r d)) = d.edge)
    {a : W} (p : H.Walk a a) (hp : p.IsCycle) : Circuit F where
  root := F.vertex a
  walk := (F.model H r he).bind p
  isCycle := (F.model H r he).bind_isCycle hp
  labels := (p.darts.map r).toFinset
  edges e := by
    simpa only [List.mem_toFinset] using F.mem_model_bind_edges H r he p e

/-- Two distinct parallel path labels lift to one simple cycle. -/
noncomputable def ofParallel (j k : J) (hne : j ≠ k)
    (he : s(F.src k,F.dst k) = s(F.src j,F.dst j)) : Circuit F := by
  have he' : s(F.src k,F.dst k) = s(F.dst j,F.src j) := he.trans (Sym2.eq_swap)
  let q := F.oriented k (F.dst j) (F.src j) he'
  have hdis : (F.path j).edges.Disjoint q.edges := by
    apply List.disjoint_left.mpr
    intro e hej heq
    exact List.disjoint_left.mp (F.edge_disjoint j k hne) hej
      ((F.mem_oriented_edges _ _ _ _ _).mp heq)
  have hmeet (x : V) (hx : x ∈ (F.path j).support) (hq : x ∈ q.support) :
      x = F.vertex (F.src j) ∨ x = F.vertex (F.dst j) :=
    F.support_inter j k hne x hx ((F.mem_oriented_support _ _ _ _ _).mp hq)
  refine ⟨F.vertex (F.src j),(F.path j).append q,?_,{j,k},?_⟩
  · exact append_isCycle_of_support_inter (F.isPath j) (F.oriented_isPath _ _ _ _)
      (fun h => F.ne j (F.injective h)) hdis hmeet
  · intro e
    simp only [Walk.edges_append,List.mem_append,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact ⟨j,Or.inl rfl,h⟩
      · exact ⟨k,Or.inr rfl,(F.mem_oriented_edges _ _ _ _ _).mp h⟩
    · rintro ⟨i,hi,h⟩
      rcases hi with rfl | rfl
      · exact Or.inl h
      · exact Or.inr ((F.mem_oriented_edges _ _ _ _ _).mpr h)

lemma disjoint_walks (C D : Circuit F) (h : Disjoint C.labels D.labels) :
    C.walk.edges.Disjoint D.walk.edges := by
  apply List.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,hi,hei⟩ := (C.edges e).mp he
  obtain ⟨j,hj,hej⟩ := (D.edges e).mp hf
  have hne : i ≠ j := by rintro rfl; exact Finset.disjoint_left.mp h hi hj
  exact List.disjoint_left.mp (F.edge_disjoint i j hne) hei hej

variable [Fintype V] {I : Type*} [Fintype I]

/-- A partition of the labels by realized circuits gives an exact-sized
cycle-only decomposition of the covered host graph. -/
lemma decomposition (C : I → Circuit F)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i).labels (C j).labels)
    (hlabels : ∀ j, ∃ i, j ∈ (C i).labels)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card = Fintype.card I := by
  let root : I → V := fun i => (C i).root
  let p : ∀ i, G.Walk (root i) (root i) := fun i => (C i).walk
  have hp : ∀ i, (p i).IsCycle := fun i => (C i).isCycle
  have hd : ∀ i j, i ≠ j → (p i).edges.Disjoint (p j).edges :=
    fun i j h => disjoint_walks F (C i) (C j) (hdis i j h)
  refine ⟨IndexedCycles.image root p,IndexedCycles.regular root p hp,
    ⟨IndexedCycles.disjoint root p hd,?_⟩,IndexedCycles.card root p hp hd⟩
  rw [← subfamilyGraph_edges]
  apply congrArg SimpleGraph.edgeSet
  apply le_antisymm (subfamilyGraph_le _)
  intro x y hxy
  obtain ⟨j,hj⟩ := hcover x y hxy
  obtain ⟨i,hi⟩ := hlabels j
  exact (IndexedCycles.edges root p s(x,y)).mpr ⟨i,(C i).edges _ |>.mpr ⟨j,hi,hj⟩⟩

lemma number_le (C : I → Circuit F)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i).labels (C j).labels)
    (hlabels : ∀ j, ∃ i, j ∈ (C i).labels)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ Fintype.card I := by
  obtain ⟨D,hD,hdec,hcard⟩ := decomposition F C hdis hlabels hcover
  rw [← hcard]
  apply Critical.number_le D _ hdec
  intro H hH
  exact Or.inl (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD H hH)

end Circuit
end Family
#print axioms Family.Circuit.ofParallel
#print axioms Family.Circuit.decomposition
#print axioms Family.Circuit.number_le
end Erdos184Work.PathSubstitution
