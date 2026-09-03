import Submission.UniversalEvenCycles
import Submission.NestedHereditary
import Submission.VertexSeparatorReduction

/-! A linear cycle bound for even graphs with nested adjacent neighborhoods. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UniversalCycles
open Critical Compression
set_option maxHeartbeats 3000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma component_degree (C : G.ConnectedComponent) (x : C.supp) :
    C.toSimpleGraph.degree x = G.degree x.val := by
  have hs : G.neighborSet x.val ⊆ C.supp := by
    intro y hy
    exact C.mem_supp_of_adj_mem_supp x.property hy
  have hd := G.degree_induce_of_neighborSet_subset (s := C.supp) (v := x) hs
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hd

lemma component_order_sum : (∑ C : G.ConnectedComponent, Fintype.card C.supp) = Fintype.card V := by
  have he : (Finset.univ.biUnion (fun C : G.ConnectedComponent => C.supp.toFinset)) =
      (Finset.univ : Finset V) := by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Set.mem_toFinset,iff_true]
    exact ⟨G.connectedComponentMk x,ConnectedComponent.connectedComponentMk_mem⟩
  have hd : ((Finset.univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).PairwiseDisjoint
      (fun C => C.supp.toFinset) := by
    intro C _ D _ hne
    exact Set.disjoint_toFinset.mpr (G.pairwise_disjoint_supp_connectedComponent hne)
  have hc := Finset.card_biUnion hd
  rw [he] at hc
  simpa only [Finset.card_univ,Set.toFinset_card] using hc.symm

lemma even_bound_of_component_universal (he : ∀ x, Even (G.degree x))
    (hu : ∀ C : G.ConnectedComponent, ∃ v : C.supp, ∀ x : C.supp,
      x ≠ v → C.toSimpleGraph.Adj v x) :
    2 * number G ≤ Fintype.card V := by
  let R := fun C : G.ConnectedComponent => C.toSimpleGraph.spanningCoe
  have hr (C : G.ConnectedComponent) : R C ≤ G := G.spanningCoe_induce_le C.supp
  have hce (C : G.ConnectedComponent) (x : C.supp) : Even (C.toSimpleGraph.degree x) := by
    rw [component_degree]
    exact he x.val
  have hRe (C : G.ConnectedComponent) (x : V) : Even ((R C).degree x) := by
    by_cases hx : x ∈ C.supp
    · have hd := Vertex.spanningCoe_degree C.toSimpleGraph ⟨x,hx⟩
      change (R C).degree x = C.toSimpleGraph.degree ⟨x,hx⟩ at hd
      rw [hd]
      exact hce C ⟨x,hx⟩
    · have hz : (R C).degree x = 0 :=
        (SimpleGraph.degree_eq_zero_iff_notMem_support (R C) x).mpr
          (fun h => hx (Vertex.spanningCoe_support_subset C.toSimpleGraph h))
      rw [hz]
      exact Even.zero
  have hdis : Pairwise (fun C D => Disjoint (R C).edgeSet (R D).edgeSet) := by
    intro C D hCD
    apply Set.disjoint_left.mpr
    intro e heC heD
    induction e using Sym2.ind with | h a b =>
    have hc := (C.adj_spanningCoe_toSimpleGraph).mp heC
    have hd := (D.adj_spanningCoe_toSimpleGraph).mp heD
    exact Set.disjoint_left.mp (G.pairwise_disjoint_supp_connectedComponent hCD) hc.1 hd.1
  have hcover : (⋃ C, (R C).edgeSet) = G.edgeSet := by
    ext e
    induction e using Sym2.ind with | h a b =>
    constructor
    · intro h
      obtain ⟨C,hC⟩ := Set.mem_iUnion.mp h
      exact hr C hC
    · intro h
      apply Set.mem_iUnion.mpr
      refine ⟨G.connectedComponentMk a,?_⟩
      exact ((G.connectedComponentMk a).adj_spanningCoe_toSimpleGraph).mpr
        ⟨ConnectedComponent.connectedComponentMk_mem,h⟩
  have hnum := BlockRestriction.number_le_sum_of_even_partition G R hr (by
    intro C x
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hRe C x) hdis hcover
  have hb (C : G.ConnectedComponent) : 2 * number (R C) ≤ Fintype.card C.supp := by
    obtain ⟨v,hv⟩ := hu C
    letI : Fintype C.supp := @Subtype.fintype V (fun x => x ∈ C.supp)
      (fun x => Classical.propDecidable _) inferInstance
    have h := universal_even_bound (G := C.toSimpleGraph) v hv (by
      intro x
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hce C x)
    have hs := VertexSeparators.number_spanning_le C.toSimpleGraph
    change number (R C) ≤ number C.toSimpleGraph at hs
    simp only [← Nat.card_eq_fintype_card] at h ⊢
    change 2 * number C.toSimpleGraph ≤ Nat.card C.supp - 1 at h
    omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun C _ => hb C)
  rw [← Finset.mul_sum, component_order_sum] at hh
  omega

lemma nested_even_bound (he : ∀ x, Even (G.degree x)) (hn : NestedAlongEdges G) :
    2 * number G ≤ Fintype.card V := by
  apply even_bound_of_component_universal he
  intro C
  exact (hn.induce C.supp).exists_universal C.connected_toSimpleGraph

end Erdos184Work.UniversalCycles
#print axioms Erdos184Work.UniversalCycles.nested_even_bound
