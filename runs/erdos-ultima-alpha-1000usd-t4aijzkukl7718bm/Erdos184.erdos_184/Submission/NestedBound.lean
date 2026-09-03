import Submission.FinitePartitionBound
import Submission.NestedEvenBound

/-! The terminal nested-neighborhood class has a uniform linear bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UniversalCycles
open Critical Compression
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma bound_of_component_universal
    (hu : ∀ C : G.ConnectedComponent, ∃ v : C.supp, ∀ x : C.supp,
      x ≠ v → C.toSimpleGraph.Adj v x) :
    number G ≤ 3 * Fintype.card V := by
  let R := fun C : G.ConnectedComponent => C.toSimpleGraph.spanningCoe
  have hr (C : G.ConnectedComponent) : R C ≤ G := G.spanningCoe_induce_le C.supp
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
  have hnum := number_le_sum_partition G R hr hdis hcover
  have hb (C : G.ConnectedComponent) : number (R C) ≤ 3 * Fintype.card C.supp := by
    obtain ⟨v,hv⟩ := hu C
    letI : Fintype C.supp := @Subtype.fintype V (fun x => x ∈ C.supp)
      (fun x => Classical.propDecidable _) inferInstance
    have h := universal_bound C.toSimpleGraph v hv
    have hs := VertexSeparators.number_spanning_le C.toSimpleGraph
    change number (R C) ≤ number C.toSimpleGraph at hs
    simp only [number_fintype_normalize,← Nat.card_eq_fintype_card] at h hs ⊢
    change canonicalNumber C.toSimpleGraph ≤ 3 * (Nat.card C.supp - 1) at h
    omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun C _ => hb C)
  rw [← Finset.mul_sum,component_order_sum] at hh
  omega

lemma nested_bound (hn : NestedAlongEdges G) : number G ≤ 3 * Fintype.card V := by
  apply bound_of_component_universal
  intro C
  exact (hn.induce C.supp).exists_universal C.connected_toSimpleGraph

end Erdos184Work.UniversalCycles
#print axioms Erdos184Work.UniversalCycles.nested_bound
