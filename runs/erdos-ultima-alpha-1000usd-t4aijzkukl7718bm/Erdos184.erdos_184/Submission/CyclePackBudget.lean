import Submission.UniversalEvenCycles
import Submission.MinimalBridgeRestoration

/-! Closing a cycle packing with a bounded number of uncovered single edges. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UniversalCycles
open Critical
set_option maxHeartbeats 1200000
variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V}

lemma cycle_pack_budget (root : I → V) (C : ∀ i, G.Walk (root i) (root i))
    (hc : ∀ i, (C i).IsCycle)
    (hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges)
    (F : Finset (Sym2 V))
    (hcover : ∀ e ∈ G.edgeSet, (∃ i, e ∈ (C i).edges) ∨ e ∈ F) :
    number G ≤ Fintype.card I + F.card := by
  let U : Finset (Sym2 V) := Finset.univ.biUnion (fun i => (C i).edges.toFinset)
  let K : SimpleGraph V := SimpleGraph.fromEdgeSet (U : Set (Sym2 V))
  have hUG : (U : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
    exact (C i).edges_subset_edgeSet (List.mem_toFinset.mp hi)
  have hK : K ≤ G := by
    intro a b hab
    exact hUG hab.1
  have hKe : K.edgeSet = (U : Set (Sym2 V)) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact Set.inter_eq_left.mpr (hUG.trans G.edgeSet_subset_setOf_not_isDiag)
  have hmem (i : I) : ∀ e ∈ (C i).edges, e ∈ K.edgeSet := by
    intro e he
    rw [hKe]
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,List.mem_toFinset.mpr he⟩
  have hnum : number K ≤ Fintype.card I := by
    apply DiminishingReturns.number_le_cycle_family root (fun i => (C i).transfer K (hmem i))
      (fun i => (hc i).transfer (hmem i))
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro e hi hj
      rw [List.mem_toFinset,Walk.edges_transfer] at hi hj
      exact hd i j hij hi hj
    · intro a b
      change s(a,b) ∈ K.edgeSet ↔ _
      rw [hKe]
      simp only [U,Finset.mem_coe,Finset.mem_biUnion,Finset.mem_univ,true_and,
        Walk.edges_transfer,List.mem_toFinset]
  have hrest : (G \ K).edgeFinset ⊆ F := by
    intro e he
    have hh := SimpleGraph.mem_edgeFinset.mp he
    rw [SimpleGraph.edgeSet_sdiff] at hh
    rcases hcover e hh.1 with ⟨i,hi⟩ | hi
    · exact (hh.2 (hmem i e hi)).elim
    · exact hi
  have hn := number_sdiff_add_le G K hK
  have hs := number_le_edges (G \ K)
  have ht := Finset.card_le_card hrest
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hs ht
  omega

end Erdos184Work.UniversalCycles
#print axioms Erdos184Work.UniversalCycles.cycle_pack_budget
