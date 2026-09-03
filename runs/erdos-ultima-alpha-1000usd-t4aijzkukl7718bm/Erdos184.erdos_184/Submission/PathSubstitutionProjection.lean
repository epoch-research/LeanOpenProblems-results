import Submission.PathSeries

/-! Even subgraphs select complete labels of an internally disjoint
path substitution. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.PathSubstitution.Family
open PathSeries
set_option maxHeartbeats 2000000
variable {V W J : Type*} [Fintype V] {G : SimpleGraph V} (F : Family J W G)

lemma internal_neighbors (j : J) (x : V) (hx : x ∈ (F.path j).support)
    (hxs : x ≠ F.vertex (F.src j)) (hxt : x ≠ F.vertex (F.dst j))
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges) :
    G.neighborSet x = (F.path j).toSubgraph.neighborSet x := by
  ext y
  constructor
  · intro hxy
    obtain ⟨i,hi⟩ := hcover x y hxy
    by_cases hij : j = i
    · subst i
      exact (F.path j).mem_edges_toSubgraph.mpr hi
    · have hxi := (F.path i).fst_mem_support_of_mem_edges hi
      exact ((F.support_inter j i hij x hx hxi).elim hxs hxt).elim
  · exact (F.path j).toSubgraph.adj_sub

lemma even_subgraph_path_all_or_none (j : J)
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (R : SimpleGraph V) (hRG : R ≤ G) (he : ∀ x, Even (R.degree x)) :
    (∀ e ∈ (F.path j).edges, e ∉ R.edgeSet) ∨
      (∀ e ∈ (F.path j).edges, e ∈ R.edgeSet) := by
  let P := (F.path j).toSubgraph.spanningCoe
  let T := R ⊓ P
  have heT (x : V) (hxs : x ≠ F.vertex (F.src j)) (hxt : x ≠ F.vertex (F.dst j)) :
      Even (T.degree x) := by
    by_cases hx : x ∈ (F.path j).support
    · have hn : T.neighborSet x = R.neighborSet x := by
        ext y
        constructor
        · exact fun h => h.1
        · intro hxy
          refine ⟨hxy,?_⟩
          have hg : y ∈ G.neighborSet x := hRG hxy
          rw [F.internal_neighbors j x hx hxs hxt hcover] at hg
          exact hg
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      rw [hn]
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he x
    · have hz : T.degree x = 0 := by
        rw [SimpleGraph.degree_eq_zero_iff_notMem_support]
        rintro ⟨y,hxy⟩
        exact hx ((F.path j).mem_verts_toSubgraph.mp ((F.path j).toSubgraph.edge_vert hxy.2))
      rw [hz]
      exact ⟨0,rfl⟩
  have hends : F.vertex (F.src j) ≠ F.vertex (F.dst j) := fun h => F.ne j (F.injective h)
  have ha := path_subgraph_all_or_none (F.path j) (F.isPath j) hends (T := T) inf_le_right (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heT)
  rcases ha with hnone | hall
  · left
    intro e heP heR
    have heT : e ∈ T.edgeSet := by
      rw [show T = R ⊓ P from rfl,SimpleGraph.edgeSet_inf]
      exact ⟨heR,(F.path j).mem_edges_toSubgraph.mpr heP⟩
    rw [hnone] at heT
    simpa using heT
  · right
    intro e heP
    have heT : e ∈ T.edgeSet := by
      rw [hall]
      exact (F.path j).mem_edges_toSubgraph.mpr heP
    rw [show T = R ⊓ P from rfl,SimpleGraph.edgeSet_inf] at heT
    exact heT.1

variable [Fintype J]
noncomputable def selectedLabels (R : SimpleGraph V) : Finset J :=
  Finset.univ.filter (fun j => (F.path j).toSubgraph.spanningCoe ≤ R)

lemma mem_selectedLabels (R : SimpleGraph V) (j : J) :
    j ∈ F.selectedLabels R ↔ ∀ e ∈ (F.path j).edges, e ∈ R.edgeSet := by
  simp only [selectedLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h e he
    exact SimpleGraph.edgeSet_mono h ((F.path j).mem_edges_toSubgraph.mpr he)
  · intro h x y hxy
    exact h s(x,y) ((F.path j).mem_edges_toSubgraph.mp hxy)

lemma even_subgraph_edges_iff
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (R : SimpleGraph V) (hRG : R ≤ G) (he : ∀ x, Even (R.degree x)) (e : Sym2 V) :
    e ∈ R.edgeSet ↔ ∃ j ∈ F.selectedLabels R, e ∈ (F.path j).edges := by
  constructor
  · intro heR
    induction e using Sym2.ind with | h x y =>
      obtain ⟨j,hj⟩ := hcover x y (hRG heR)
      refine ⟨j,?_,hj⟩
      rw [F.mem_selectedLabels]
      rcases F.even_subgraph_path_all_or_none j hcover R hRG he with hn | ha
      · exact (hn s(x,y) hj heR).elim
      · exact ha
  · rintro ⟨j,hj,hej⟩
    exact (F.mem_selectedLabels R j).mp hj e hej

lemma even_subgraph_edgeFinset
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (R : SimpleGraph V) (hRG : R ≤ G) (he : ∀ x, Even (R.degree x)) :
    R.edgeFinset = (F.selectedLabels R).biUnion (fun j => (F.path j).edges.toFinset) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset,Finset.mem_biUnion,List.mem_toFinset]
  exact F.even_subgraph_edges_iff hcover R hRG he e

#print axioms even_subgraph_edgeFinset
end Erdos184Work.PathSubstitution.Family
