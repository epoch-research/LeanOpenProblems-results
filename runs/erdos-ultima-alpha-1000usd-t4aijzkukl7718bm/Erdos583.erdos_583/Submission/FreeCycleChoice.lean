import Submission.TailIntegrated

/-! Cycle minimization compatible with the free tail and carrier optima.
The endpoint quotas, and their square energy, are not constrained. -/
namespace Erdos583FreeCycleChoiceDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.LollipopEar Erdos583Work.TrailNormalization
open Erdos583Work.CarrierCount Erdos583Work.CarrierLength
open Erdos583Work.MemberExpansion Erdos583Work.VertexCritical
open Erdos583Work.MemberNormalExpansion
open Erdos583Work.CyclePrefixRepair
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma exists_free_shortest_cycle (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧
      ∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → M.cycle.length ≤ N.cycle.length := by
  let P (n : ℕ) := ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
    U.score=T.score ∧ M.cycle.length=n
  have hex : ∃ n, P n := ⟨L.cycle.length,T,L,rfl,rfl⟩
  obtain ⟨U,M,hUs,hL⟩ := Nat.find_spec hex
  refine ⟨U,M,hUs,?_⟩
  intro W N hWs
  rw [hL]
  exact Nat.find_min' hex ⟨W,N,hWs.trans hUs,rfl⟩

lemma exists_cycle_tail_carrier_optimum (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) :
    ∃ U : TrailFamily G k, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧
      (∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → M.cycle.length ≤ N.cycle.length) ∧
      (∀ W : TrailFamily G k, ∀ N : RootedCycleRep W r,
        W.score=U.score → N.cycle=M.cycle → M.tail.length ≤ N.tail.length) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk M.index).toSubgraph=(U.walk M.index).toSubgraph →
        carrierCount W (U.walk M.index).toSubgraph.verts ≤ carrierCount U (U.walk M.index).toSubgraph.verts) ∧
      (∀ W : TrailFamily G k, W.score=U.score →
        (W.walk M.index).toSubgraph=(U.walk M.index).toSubgraph →
        carrierCount W (U.walk M.index).toSubgraph.verts=carrierCount U (U.walk M.index).toSubgraph.verts →
        carrierLength U (U.walk M.index).toSubgraph.verts ≤ carrierLength W (U.walk M.index).toSubgraph.verts) := by
  obtain ⟨R,N,hRs,hC⟩ := exists_free_shortest_cycle T r L
  obtain ⟨U,M,hUs,hMC,hTail,hMax,hMin⟩ := JointTailCarrier.exists_joint_optimum R r N
  refine ⟨U,M,hUs.trans hRs,?_,hTail,hMax,hMin⟩
  intro W P hWs
  rw [hMC]
  exact hC W P (hWs.trans hUs)

lemma free_cycle_minimum_structure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) (hdeg : 3 ≤ Nat.card (G.neighborSet r))
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → L.cycle.length ≤ M.cycle.length) :
    L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x) := by
  by_cases h3 : L.cycle.length=3
  · exact Or.inl h3
  · right
    intro x hxC
    have hc3 := L.isCycle.three_le_length
    have h2 := NormalRemainder.cycle_degree_ge_two L.cycle L.isCycle hxC
    have hn := shortest_rooted_cycle_no_degree_two hsmall hG hfail T r L hs
      (maximum_of_one_defect_failure hfail T hs) (fun W M hWs _ ↦ hmin W M hWs) hdeg (by omega) hxC
    by_contra hlt
    exact hn (by omega)

lemma free_cycle_tail_normal_complement {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) (hdeg : 3 ≤ Nat.card (G.neighborSet r))
    (hCmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hTmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) :
    (selectedGraph T (Finset.univ.erase L.index)).supportᶜ.ncard ≤ 1 := by
  exact NormalRemainderOne.normal_support_compl_card_le_one hsmall hG hfail T r L hs
    (maximum_of_one_defect_failure hfail T hs) hdeg
    (free_cycle_minimum_structure hsmall hG hfail T hs r L hdeg hCmin)
    (fun W M hWs _ hMC ↦ hTmin W M hWs hMC)


lemma normal_support_spanning_of_cycle_degree_three [Fintype V] (T : TrailFamily G k)
    (hG : G.Connected) (i : Fin k) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hdeg : ∀ x ∈ C.support, 3 ≤ Nat.card (G.neighborSet x)) :
    (selectedGraph T (Finset.univ.erase i)).support=Set.univ := by
  classical
  letI : Nontrivial V := ⟨⟨a,C.snd,(C.adj_snd hC.not_nil).ne⟩⟩
  apply Set.eq_univ_of_forall
  intro v
  by_contra hv
  have hvG : v ∈ G.support := hG.preconnected.support_eq_univ.symm ▸ Set.mem_univ v
  have hvC : v ∈ C.support := by
    have hh := NormalRemainder.missing_mem_removed T i hvG hv
    rwa [←Walk.mem_verts_toSubgraph,hi,Walk.mem_verts_toSubgraph] at hh
  have he : G.neighborSet v=C.toSubgraph.neighborSet v := by
    ext w
    constructor
    · intro hw
      obtain ⟨j,hj⟩ := (T.cover s(v,w)).mp hw
      by_cases hji : j=i
      · subst j; rwa [hi] at hj
      · exact (hv ⟨w,j,by simp [hji],hj⟩).elim
    · exact C.toSubgraph.adj_sub
  have hb := hdeg v hvC
  rw [he,Nat.card_coe_set_eq,hC.ncard_neighborSet_toSubgraph_eq_two hvC] at hb
  omega

lemma free_minimum_whole_cycle_spanning {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) (hdeg : 3 ≤ Nat.card (G.neighborSet r))
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → L.cycle.length ≤ M.cycle.length) (hn : L.tail.Nil) :
    (selectedGraph T (Finset.univ.erase L.index)).support=Set.univ := by
  have he : (T.walk L.index).toSubgraph=L.cycle.toSubgraph := by
    have hz : ∀ {a b c : Fin n} (P : G.Walk a b) (Q : G.Walk b c), Q.Nil →
        (P.append Q).toSubgraph=P.toSubgraph := by
      intro a b c P Q hQ
      cases hQ
      simp
    rw [L.subgraph]
    exact hz L.cycle L.tail hn
  have hl := HeptagonExclusion.whole_cycle_length_ge_eight hsmall hG hfail T hs
    (maximum_of_one_defect_failure hfail T hs) L.index L.cycle L.isCycle he
  have hcases := free_cycle_minimum_structure hsmall hG hfail T hs r L hdeg hmin
  exact normal_support_spanning_of_cycle_degree_three T hG L.index L.cycle L.isCycle he
    (hcases.resolve_left (by omega))


lemma free_cycle_tail_cubic_support {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) (hdeg : Nat.card (G.neighborSet r)=3)
    (hCmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → L.cycle.length ≤ M.cycle.length)
    (hTmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : RootedCycleRep W r,
      W.score=T.score → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) (hn : ¬L.tail.Nil) :
    (selectedGraph T (Finset.univ.erase L.index)).support=({r}ᶜ : Set (Fin n)) := by
  have hb := free_cycle_tail_normal_complement hsmall hG hfail T hs r L (by omega) hCmin hTmin
  have hsub := Set.ncard_le_one_iff_subsingleton.mp hb
  have hr : r ∉ (selectedGraph T (Finset.univ.erase L.index)).support := by
    rintro ⟨y,j,hj,hrj⟩
    exact FreeTailGroups.cubic_open_root_others_avoid T r L hs
      (maximum_of_one_defect_failure hfail T hs) hdeg hn j (Finset.mem_erase.mp hj).1
      (Walk.mem_support_of_adj_toSubgraph hrj)
  ext v
  constructor
  · intro hv
    exact fun he ↦ hr ((Set.mem_singleton_iff.mp he) ▸ hv)
  · intro hv
    by_contra hno
    exact hv (Set.mem_singleton_iff.mpr (hsub hno hr))

lemma exists_free_cycle_component_certificate {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hcritical : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r) (hdeg : 3 ≤ Nat.card (G.neighborSet r)) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∃ M : RootedCycleRep U r,
      U.score=T.score ∧
      (M.cycle.length=3 ∨ ∀ x ∈ M.cycle.support, 3 ≤ Nat.card (G.neighborSet x)) ∧
      (selectedGraph U (Finset.univ.erase M.index)).supportᶜ.ncard ≤ 1 ∧
      (M.tail.Nil → (selectedGraph U (Finset.univ.erase M.index)).support=Set.univ) ∧
      (Odd n → (selectedGraph U (Finset.univ.erase M.index)).support=Set.univ) ∧
      (Nat.card (G.neighborSet r)=3 → ¬M.tail.Nil →
        (selectedGraph U (Finset.univ.erase M.index)).support=({r}ᶜ : Set (Fin n))) ∧
      Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 3 ∧
      (Odd n → Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      (Nat.card (G.neighborSet r)=3 → ¬M.tail.Nil →
        Nat.card (MemberComponents.normalGraph U M.index).ConnectedComponent ≤ 2) ∧
      M.cycle.length+M.tail.length ≤
        2*(CarrierGroups.carrierIndices U M.index (U.walk M.index).toSubgraph.verts).card+2 ∧
      M.cycle.length+M.tail.length+
        Nat.card (GroupComponents.inducedGraph U (OutsideCarrierBudget.outsideIndices U (U.walk M.index).toSubgraph.verts)).ConnectedComponent ≤
        2*(CarrierGroups.carrierIndices U M.index (U.walk M.index).toSubgraph.verts).card+3 := by
  obtain ⟨U,M,hUs,hCmin,hTmin,hMax,hMin⟩ := exists_cycle_tail_carrier_optimum T r L
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
  refine ⟨U,M,hUs,free_cycle_minimum_structure hsmall hG hfail U hsU r M hdeg hCmin,
    free_cycle_tail_normal_complement hsmall hG hfail U hsU r M hdeg hCmin hTmin,
    free_minimum_whole_cycle_spanning hsmall hG hfail U hsU r M hdeg hCmin,
    (fun ho ↦ TailEar.odd_normal_support_spanning hsmall ho hG hfail U r M hsU
      (maximum_of_one_defect_failure hfail U hsU)),
    (fun hd hn ↦ free_cycle_tail_cubic_support hsmall hG hfail U hsU r M hd hCmin hTmin hn),
    FreeTailAbsorption.normal_component_count_le_three hsmall hG hfail hcritical U hsU r M hTmin,
    FreeTailAbsorption.odd_normal_component_count_le_two hsmall hG hfail hcritical U hsU r M hTmin,
    FreeTailAbsorption.cubic_open_component_count_le_two hsmall hG hfail hcritical U hsU r M hTmin,?_,?_⟩
  · have hh := hAB.1
    rwa [hv] at hh
  · have hh := hCB.1
    rwa [hv] at hh

end Erdos583FreeCycleChoiceDevelopment
