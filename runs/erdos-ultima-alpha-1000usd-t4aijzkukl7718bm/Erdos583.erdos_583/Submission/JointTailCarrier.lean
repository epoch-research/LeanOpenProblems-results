import Submission.FreeTailAbsorption

/-! Compatible free-tail and fixed-anchor carrier optimization.
No quota-energy constraint is added or claimed to survive. -/
namespace Erdos583JointTailCarrierDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization Erdos583Work.LollipopEar
open Erdos583Work.CarrierCount Erdos583Work.CarrierLength Erdos583Work.CarrierGroups
open Erdos583Work.OutsideCarrierBudget Erdos583Work.AnchorCarrier Erdos583Work.AnchorComponentBudget
open Erdos583FreeTailAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma exists_joint_optimum (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧
      (∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → N.cycle=M.cycle → M.tail.length ≤ N.tail.length) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk M.index).toSubgraph=(U.walk M.index).toSubgraph →
        carrierCount W (U.walk M.index).toSubgraph.verts ≤ carrierCount U (U.walk M.index).toSubgraph.verts) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk M.index).toSubgraph=(U.walk M.index).toSubgraph →
        carrierCount W (U.walk M.index).toSubgraph.verts=carrierCount U (U.walk M.index).toSubgraph.verts →
        carrierLength U (U.walk M.index).toSubgraph.verts ≤ carrierLength W (U.walk M.index).toSubgraph.verts) := by
  obtain ⟨R,N,hRs,hNC,hTail⟩ := exists_shortest_tail T r L
  let K := (R.walk N.index).toSubgraph
  obtain ⟨A,hAs,hAi,hMax,hMin⟩ := AnchorCarrier.exists_shortest_maximum_carriers R N.index K rfl
  have hP : (N.cycle.append N.tail).IsTrail := trail_append_of_disjoint N.isCycle.isTrail N.isPath.isTrail
    (edge_disjoint_of_one_common_vertex _ _ N.inter)
  obtain ⟨U,hUs,hUa,hUb,hparts,_⟩ := replace_one_general A N.index (N.cycle.append N.tail) hP
    (N.subgraph.symm.trans hAi.symm)
  let M : RootedCycleRep U r :=
    ⟨N.index,N.finish,hUa,hUb,N.cycle,N.tail,N.isCycle,N.isPath,N.inter,
      (hparts N.index).trans (hAi.trans N.subgraph)⟩
  have hUi : (U.walk N.index).toSubgraph=K := (hparts N.index).trans hAi
  have hCount : carrierCount U K.verts=carrierCount A K.verts := by
    apply carrierCount_congr
    intro j
    rw [hparts]
  have hLength : carrierLength U K.verts=carrierLength A K.verts := by
    unfold carrierLength
    apply Finset.sum_congr rfl
    intro j _
    exact carrier_weight_of_same_subgraph A U K.verts j (hparts j)
  refine ⟨U,M,hUs.trans (hAs.trans hRs),hNC,?_,?_,?_⟩
  · intro W P hWs hPC
    exact hTail W P (hWs.trans (hUs.trans hAs)) hPC
  · intro W hWs hWi
    change (W.walk N.index).toSubgraph=(U.walk N.index).toSubgraph at hWi
    rw [hUi] at hWi
    change carrierCount W (U.walk N.index).toSubgraph.verts ≤ carrierCount U (U.walk N.index).toSubgraph.verts
    rw [hUi,hCount]
    exact hMax W (hWs.trans hUs) hWi
  · intro W hWs hWi hWc
    change (W.walk N.index).toSubgraph=(U.walk N.index).toSubgraph at hWi
    rw [hUi] at hWi
    change carrierCount W (U.walk N.index).toSubgraph.verts=carrierCount U (U.walk N.index).toSubgraph.verts at hWc
    rw [hUi,hCount] at hWc
    change carrierLength U (U.walk N.index).toSubgraph.verts ≤ carrierLength W (U.walk N.index).toSubgraph.verts
    rw [hUi,hLength]
    exact hMin W (hWs.trans hUs) hWi hWc

lemma exists_joint_component_certificate {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧ M.cycle=L.cycle ∧
      Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 3 ∧
      (Odd n → Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      (Nat.card (G.neighborSet r)=3 → ¬M.tail.Nil →
        Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      M.cycle.length+M.tail.length ≤ 2*(carrierIndices U M.index (U.walk M.index).toSubgraph.verts).card+2 ∧
      M.cycle.length+M.tail.length+
        Nat.card (GroupComponents.inducedGraph U (outsideIndices U (U.walk M.index).toSubgraph.verts)).ConnectedComponent ≤
        2*(carrierIndices U M.index (U.walk M.index).toSubgraph.verts).card+3 ∧
      (Odd n → M.cycle.length+M.tail.length+
        Nat.card (GroupComponents.inducedGraph U (outsideIndices U (U.walk M.index).toSubgraph.verts)).ConnectedComponent ≤
        2*(carrierIndices U M.index (U.walk M.index).toSubgraph.verts).card+2) := by
  obtain ⟨U,M,hUs,hMC,hTail,hMax,hMin⟩ := exists_joint_optimum T r L
  have hsU : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by omega
  have hnK : ¬IsPathSubgraph (U.walk M.index).toSubgraph := by
    rintro ⟨a,b,P,hP,hPe⟩
    exact M.member_not_path (ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail M.index) hP hPe)
  have hAB := AnchorCarrier.optimized_anchor_size_bound hsmall hG hfail U hsU M.index
    (U.walk M.index).toSubgraph hnK rfl hMax hMin
  have hCB := AnchorComponentBudget.anchor_component_budget hsmall hG hfail U hsU M.index
    (U.walk M.index).toSubgraph hnK rfl hMax hMin
  have hv : (U.walk M.index).toSubgraph.verts.ncard=M.cycle.length+M.tail.length := by
    rw [M.subgraph,LollipopEar.lollipop_vertex_card M.cycle M.isCycle M.tail M.isPath M.inter,Walk.length_append]
  refine ⟨U,M,hUs,hMC,
    normal_component_count_le_three hsmall hG hfail hcritical U hsU r M hTail,
    odd_normal_component_count_le_two hsmall hG hfail hcritical U hsU r M hTail,
    cubic_open_component_count_le_two hsmall hG hfail hcritical U hsU r M hTail,?_,?_,?_⟩
  · have hh := hAB.1
    rwa [hv] at hh
  · have hh := hCB.1
    rwa [hv] at hh
  · intro ho
    have hh := hCB.2 ho
    rwa [hv] at hh

end Erdos583JointTailCarrierDevelopment
