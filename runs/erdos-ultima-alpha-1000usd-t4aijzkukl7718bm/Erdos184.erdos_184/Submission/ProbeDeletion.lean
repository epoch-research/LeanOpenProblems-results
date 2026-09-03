import Submission.StarDeletion

/-! Exact edge-deletion formula for even graphs. This is a local identity,
not a uniform bound on cycle-and-edge decompositions. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ExactEdgeDeletion
open Critical MaximumCycles Subfamilies
set_option maxHeartbeats 1500000
set_option profiler true
set_option profiler.threshold 1000
set_option synthInstance.maxSize 10000
variable {V : Type*} [Fintype V]

lemma cycle_upper_bound {G : SimpleGraph V} {a b u : V}
    (p : G.Walk u u) (hp : p.IsCycle) (he : p.toSubgraph.Adj a b) :
    number (G.deleteEdges {s(a,b)}) + 1 ≤
      number (G \ p.toSubgraph.spanningCoe) + p.length := by
  run_tac do IO.eprintln "upper-start"
  let C := p.toSubgraph.spanningCoe
  let K := G \ C
  let F := C.deleteEdges {s(a,b)}
  have hU : K ⊔ F = G.deleteEdges {s(a,b)} := by
    ext x y
    change (G.Adj x y ∧ ¬ C.Adj x y) ∨ F.Adj x y ↔ _
    simp only [F,SimpleGraph.deleteEdges_adj]
    have hCG : C.Adj x y → G.Adj x y := p.toSubgraph.adj_sub
    have hab : s(a,b) ∈ C.edgeSet := he
    have hnot : ¬ C.Adj x y → s(x,y) ∉ ({s(a,b)} : Set (Sym2 V)) := by
      intro hn heq
      exact hn (show s(x,y) ∈ C.edgeSet from (Set.mem_singleton_iff.mp heq).symm ▸ hab)
    change (G.Adj x y ∧ ¬ C.Adj x y) ∨
        (C.Adj x y ∧ s(x,y) ∉ ({s(a,b)} : Set (Sym2 V))) ↔ _
    tauto
  have hd : Disjoint K.edgeSet F.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heK heF
    rw [SimpleGraph.edgeSet_sdiff] at heK
    rw [SimpleGraph.edgeSet_deleteEdges] at heF
    exact heK.2 heF.1
  have hn := CycleForestCertificate.number_sup_le hd
  have hf := number_le_edges F
  have hc : F.edgeFinset.card + 1 = p.length := by
    have hcount := cycle_edge_count G hp
    have heC : s(a,b) ∈ C.edgeFinset := SimpleGraph.mem_edgeFinset.mpr he
    have hfin : F.edgeFinset = C.edgeFinset.erase s(a,b) := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_deleteEdges,
        Finset.mem_erase,Set.mem_diff,Set.mem_singleton_iff,F]
      tauto
    rw [hfin,Finset.card_erase_add_one heC]
    exact hcount
  rw [hU] at hn
  change number (G.deleteEdges {s(a,b)}) + 1 ≤ number K + p.length
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hf hc
  omega

end Erdos184Work.ExactEdgeDeletion
#print axioms Erdos184Work.ExactEdgeDeletion.cycle_upper_bound
