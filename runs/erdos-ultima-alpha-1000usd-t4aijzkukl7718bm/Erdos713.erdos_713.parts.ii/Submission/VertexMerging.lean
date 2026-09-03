import FormalConjecturesUtil

/-! Identifying nonadjacent vertices loses exactly their common-neighbor count. -/
open SimpleGraph Finset
namespace Erdos713VertexMerging
variable {V W : Type*}
set_option maxHeartbeats 2000000

def mergeOn (G : SimpleGraph V) (u v : V) (hn : ¬ G.Adj u v) : SimpleGraph V where
  Adj x y := x ≠ v ∧ y ≠ v ∧
    (G.Adj x y ∨ (x = u ∧ G.Adj v y) ∨ (y = u ∧ G.Adj v x))
  symm x y := by
    rintro ⟨hx,hy,h | h | h⟩
    · exact ⟨hy,hx,Or.inl h.symm⟩
    · exact ⟨hy,hx,Or.inr (Or.inr h)⟩
    · exact ⟨hy,hx,Or.inr (Or.inl h)⟩
  loopless x := by
    rintro ⟨_,_,h | ⟨rfl,h⟩ | ⟨rfl,h⟩⟩
    · exact h.ne rfl
    · exact hn h.symm
    · exact hn h.symm

def merge (G : SimpleGraph V) (u v : V) (hn : ¬ G.Adj u v) :
    SimpleGraph {x : V // x ≠ v} := (mergeOn G u v hn).induce {x | x ≠ v}

lemma merge_adj (G : SimpleGraph V) (u v : V) (hn : ¬ G.Adj u v)
    (x y : {x : V // x ≠ v}) :
    (merge G u v hn).Adj x y ↔ G.Adj x.val y.val ∨
      (x.val = u ∧ G.Adj v y.val) ∨ (y.val = u ∧ G.Adj v x.val) := by
  change (x.val ≠ v ∧ y.val ≠ v ∧ _) ↔ _
  exact ⟨fun h => h.2.2,fun h => ⟨x.property,y.property,h⟩⟩

open scoped Classical in
noncomputable def newNeighbors [Fintype V] (G : SimpleGraph V) (u v : V) : Finset V :=
  (G.neighborFinset v) \ (G.neighborFinset u)

open scoped Classical in
noncomputable def newEdges [Fintype V] (G : SimpleGraph V) (u v : V) : Finset (Sym2 V) :=
  (newNeighbors G u v).image (fun x => s(u,x))

lemma mem_newNeighbors [Fintype V] (G : SimpleGraph V) (u v x : V) :
    x ∈ newNeighbors G u v ↔ G.Adj v x ∧ ¬ G.Adj u x := by
  classical
  simp [newNeighbors]

lemma mem_newEdges [Fintype V] (G : SimpleGraph V) (u v x y : V) :
    s(x,y) ∈ newEdges G u v ↔
      (x = u ∧ G.Adj v y ∧ ¬ G.Adj u y) ∨
      (y = u ∧ G.Adj v x ∧ ¬ G.Adj u x) := by
  classical
  simp only [newEdges,mem_image,mem_newNeighbors,Sym2.eq_iff]
  constructor
  · rintro ⟨z,hz,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact Or.inl ⟨rfl,hz⟩
    · exact Or.inr ⟨rfl,hz⟩
  · rintro (⟨rfl,hy⟩ | ⟨rfl,hx⟩)
    · exact ⟨y,hy,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨x,hx,Or.inr ⟨rfl,rfl⟩⟩

open scoped Classical in
lemma mergeOn_edgeFinset [Fintype V] (G : SimpleGraph V) {u v : V}
    (huv : u ≠ v) (hn : ¬ G.Adj u v) :
    (mergeOn G u v hn).edgeFinset = (G.deleteIncidenceSet v).edgeFinset ∪ newEdges G u v := by
  classical
  ext e
  induction e using Sym2.ind with | _ x y =>
  simp only [mem_edgeFinset,mem_edgeSet,mem_union,deleteIncidenceSet_adj,mem_newEdges]
  change (x ≠ v ∧ y ≠ v ∧ (G.Adj x y ∨ (x = u ∧ G.Adj v y) ∨ (y = u ∧ G.Adj v x))) ↔ _
  constructor
  · rintro ⟨hx,hy,hxy | ⟨rfl,hvy⟩ | ⟨rfl,hvx⟩⟩
    · exact Or.inl ⟨hxy,hx,hy⟩
    · by_cases huy : G.Adj x y
      · exact Or.inl ⟨huy,hx,hy⟩
      · exact Or.inr (Or.inl ⟨rfl,hvy,huy⟩)
    · by_cases hux : G.Adj y x
      · exact Or.inl ⟨hux.symm,hx,hy⟩
      · exact Or.inr (Or.inr ⟨rfl,hvx,hux⟩)
  · rintro (⟨hxy,hx,hy⟩ | ⟨rfl,hvy,_⟩ | ⟨rfl,hvx,_⟩)
    · exact ⟨hx,hy,Or.inl hxy⟩
    · exact ⟨huv,hvy.ne.symm,Or.inr (Or.inl ⟨rfl,hvy⟩)⟩
    · exact ⟨hvx.ne.symm,huv,Or.inr (Or.inr ⟨rfl,hvx⟩)⟩

open scoped Classical in
lemma newEdges_disjoint [Fintype V] (G : SimpleGraph V) (u v : V) :
    Disjoint (G.deleteIncidenceSet v).edgeFinset (newEdges G u v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hn
  induction e using Sym2.ind with | _ x y =>
  have hg : G.Adj x y := (deleteIncidenceSet_adj.mp (mem_edgeFinset.mp he)).1
  rcases (mem_newEdges G u v x y).mp hn with ⟨rfl,_,h⟩ | ⟨rfl,_,h⟩
  · exact h hg
  · exact h hg.symm

open scoped Classical in
lemma newEdges_card [Fintype V] (G : SimpleGraph V) (u v : V) :
    (newEdges G u v).card = (newNeighbors G u v).card := by
  classical
  apply card_image_of_injective
  intro x y h
  rcases Sym2.eq_iff.mp h with ⟨_,h⟩ | ⟨h1,h2⟩
  · exact h
  · exact h2.trans h1

open scoped Classical in
lemma merge_edge_count [Fintype V] (G : SimpleGraph V) {u v : V}
    (huv : u ≠ v) (hn : ¬ G.Adj u v) :
    Nat.card (merge G u v hn).edgeSet + Nat.card (G.commonNeighbors u v) = Nat.card G.edgeSet := by
  classical
  have hs : (mergeOn G u v hn).support ⊆ {x | x ≠ v} := by
    rintro x ⟨y,hxy⟩
    exact hxy.1
  have he := (mergeOn G u v hn).card_edgeFinset_induce_of_support_subset hs
  have hc : ((G.neighborFinset u) ∩ (G.neighborFinset v)).card = Nat.card (G.commonNeighbors u v) := by
    rw [Nat.card_eq_fintype_card,← Set.toFinset_card]
    congr 1
    ext x
    simp [mem_commonNeighbors]
  have hdeg := G.degree_le_card_edgeFinset v
  have hcom : Nat.card (G.commonNeighbors u v) ≤ G.degree v := by
    simpa only [Nat.card_eq_fintype_card] using G.card_commonNeighbors_le_degree_right u v
  rw [mergeOn_edgeFinset G huv hn,card_union_of_disjoint (newEdges_disjoint G u v),
    card_edgeFinset_deleteIncidenceSet,newEdges_card,newNeighbors,card_sdiff,hc,
    card_neighborFinset_eq_degree] at he
  change (merge G u v hn).edgeFinset.card = _ at he
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at he hdeg
  omega

#print axioms merge_edge_count
end Erdos713VertexMerging
