import Submission.StarCopyIntegrated
open SimpleGraph
namespace Erdos583Work
set_option Elab.async false
set_option maxHeartbeats 2400000
/-- Diagnostic only: test whether the accumulated final-branch arithmetic closes. -/
theorem final_branch_diagnostic {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsPathSubgraph H) ∧
      IsDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
  classical
  by_contra hn
  have hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
    simpa only [GoodDecomposition,and_assoc] using hn
  obtain ⟨n,hnorder,J,hJ,hfailJ,hsmall⟩ :=
    VertexCritical.failure_has_minimal_order G hG hfail
  obtain ⟨H,hH,hfailH,hglobal,hcritical,r₀,T₀,hscore₀,hroot₀,hmax₀⟩ :=
    GlobalCritical.failure_has_global_minimal_root J hJ hfailJ
  have hproperInduced (S : Set (Fin n)) (hc : S.ncard < n)
      (hs : (H.induce S).Connected) := hsmall.on_induce H S hc hs
  have hbridgeStructure {u v : Fin n} (hb : H.IsBridge s(u,v)) :=
    hsmall.bridge_structure hH hfailH hb
  have hbridgeBalanced {u v : Fin n} (hb : H.IsBridge s(u,v)) :=
    MarkedDouble.failure_bridge_balanced hsmall hH hfailH hb
  have hbridgeEdgeBalance (S : Set (Fin n)) {u v : Fin n}
      (h : H.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
      (hcross : ∀ x ∈ S, ∀ y ∉ S, H.Adj x y → x=u ∧ y=v)
      (hS : 2 ≤ S.ncard) (hcS : 2 ≤ Sᶜ.ncard) :=
    GlobalCritical.failure_cut_edges_equal hsmall hH hfailH hglobal S h hu hv hcross hS hcS
  have hnonleafBridgeOddEdges {u v : Fin n} (hb : H.IsBridge s(u,v))
      (hu : Nat.card (H.neighborSet u) ≠ 1) (hv : Nat.card (H.neighborSet v) ≠ 1) :=
    GlobalCritical.nonleaf_bridge_odd_edge_count hsmall hH hfailH hglobal hb hu hv
  have honeLeafEvenEdges (he : Even H.edgeSet.ncard) :=
    GlobalCritical.one_leaf_of_even_edge_count hsmall hH hfailH hglobal he
  have hnonleafBridgeUnique {u v a b : Fin n}
      (huv : H.IsBridge s(u,v)) (hab : H.IsBridge s(a,b))
      (hu : Nat.card (H.neighborSet u) ≠ 1) (hv : Nat.card (H.neighborSet v) ≠ 1)
      (ha : Nat.card (H.neighborSet a) ≠ 1) (hb : Nat.card (H.neighborSet b) ≠ 1) :=
    BalancedBridge.nonleaf_bridge_unique_of_failure hsmall hH hfailH huv hab hu hv ha hb
  have hleafAtBridge {u v w a : Fin n} (hb : H.IsBridge s(u,v))
      (hu : Nat.card (H.neighborSet u) ≠ 1) (hv : Nat.card (H.neighborSet v) ≠ 1)
      (hwa : H.Adj w a) (hw : ∀ x, H.Adj w x → x=a) :=
    BridgeLeafLocation.leaf_attached_to_nonleaf_bridge hsmall hH hfailH hb hu hv hwa hw
  have hleafModulo (hn4 : ¬4 ∣ n) :=
    BalancedBridge.one_leaf_unless_four_dvd hsmall hH hfailH hn4
  have hbridgeParity {u v : Fin n} (hb : H.IsBridge s(u,v)) :=
    hsmall.bridge_even_order_or_leaf hH hfailH hb
  have hbridgeSidesComplex {u v : Fin n} (hb : H.IsBridge s(u,v)) :=
    MarkedBudgets.failure_bridge_side_structure hsmall hH hfailH hb
  have hbridgeEnds {u v : Fin n} (hb : H.IsBridge s(u,v)) :=
    BridgeParityReduction.bridge_endpoints_odd_of_failure hsmall hH hfailH hb
  have hevenNoBridge {u : Fin n} (hu : Even (Nat.card (H.neighborSet u))) (v : Fin n) :=
    BridgeParityReduction.even_vertex_no_bridge_of_failure hsmall hH hfailH hu v
  have hleafCount := LeafPairReduction.at_most_two_leaves_of_failure hsmall hH hfailH
  have hleafNeighbors {u v a b : Fin n} (huv : u ≠ v)
      (ha : H.Adj u a) (hb : H.Adj v b)
      (hu : ∀ x, H.Adj u x → x=a) (hv : ∀ x, H.Adj v x → x=b) :=
    LeafPairReduction.leaf_neighbors_bridge_of_failure hsmall hH hfailH huv ha hb hu hv
  have hleafCubic {u v : Fin n} (huv : H.Adj u v)
      (hu : ∀ x, H.Adj u x → x=v) (hd : Nat.card (H.neighborSet v)=3) :=
    LeafCubicReduction.leaf_cubic_triangle_of_failure hsmall hH hfailH huv hu hd
  have hleafCubicOdd {u v : Fin n} (huv : H.Adj u v)
      (hu : ∀ x, H.Adj u x → x=v) (hd : Nat.card (H.neighborSet v)=3) :=
    LeafCubicEven.cubic_leaf_neighbors_odd hsmall hH hfailH huv hu hd
  have hleafTipDisjoint {u v : Fin n}
      (hu : Nat.card (H.neighborSet u)=1) (hv : Nat.card (H.neighborSet v)=2) :=
    LeafTipSeparation.leaf_tip_neighbors_disjoint hsmall hH hfailH hu hv
  have htwoLeafDegree {u v a b : Fin n} (huv : u ≠ v)
      (ha : H.Adj u a) (hb : H.Adj v b)
      (hu : ∀ x, H.Adj u x → x=a) (hv : ∀ x, H.Adj v x → x=b) :=
    LeafCubicReduction.two_leaf_neighbors_degree_ge_five hsmall hH hfailH huv ha hb hu hv
  have hoddBridgeless (ho : Odd n) :=
    LeafReduction.bridgeless_of_odd_failure hsmall ho hH hfailH
  have hoddDeleteVertex (ho : Odd n) (u : Fin n) :=
    CutVertexReduction.delete_vertex_connected_of_odd_failure hsmall ho hH hfailH u
  have hevenDeleteVertex (u : Fin n) (hu : Even (Nat.card (H.neighborSet u))) :=
    CutVertexParity.delete_even_vertex_connected_of_failure hsmall hH hfailH u hu
  have hcutVertexParity (S : Set (Fin n)) (u : Fin n) (hu : u ∈ S)
      (hcross : ∀ x ∈ S, ∀ y ∉ S, H.Adj x y → x=u)
      (hS : 3 ≤ S.ncard) (hcS : 2 ≤ Sᶜ.ncard) :=
    CutVertexParity.nontrivial_cut_side_parity hsmall hH hfailH S u hu hcross hS hcS
  have hdeleteComponentCount (u : Fin n) :=
    CutComponentBound.at_most_three_components_after_delete_vertex hsmall hH hfailH u
  have hthreeComponentsLeaf (u : Fin n)
      (hthree : Nat.card (H.induce ({u}ᶜ : Set (Fin n))).ConnectedComponent=3) :=
    CutComponentBound.three_components_imply_leaf_at_vertex hsmall hH hfailH u hthree
  have hdegreeTwo {u : Fin n} (hd : Nat.card (H.neighborSet u)=2) :=
    DegreeTwoReduction.degree_two_triangle hsmall hH hfailH hd
  have hdegreeTwoNeighbors {x u : Fin n} (hxu : H.Adj x u)
      (hx : Nat.card (H.neighborSet x)=2) :=
    LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hH hfailH hxu hx
  have hdegreeTwoDisjoint {u v : Fin n} (huv : u ≠ v)
      (hu : Nat.card (H.neighborSet u)=2) (hv : Nat.card (H.neighborSet v)=2) :=
    DegreeTwoPacking.degree_two_closed_neighbors_disjoint hsmall hH hfailH huv hu hv
  have hdegreeTwoCount := DegreeTwoSeparation.degree_two_card_bound_strict hsmall hH hfailH
  have hdegreeTwoSeparation {u v a c : Fin n} (huv : u ≠ v)
      (hu : Nat.card (H.neighborSet u)=2) (hv : Nat.card (H.neighborSet v)=2)
      (hua : H.Adj u a) (hvc : H.Adj v c) (hac : H.Adj a c) :=
    DegreeTwoSeparation.degree_two_cross_edge_bridge hsmall hH hfailH huv hu hv hua hvc hac
  have houtsideDegreeTwo := DegreeTwoSeparation.two_outside_tip_region hsmall hH hfailH
  have hpathOddComponent {a b : Fin n} (P : H.Walk a b) (hp : P.IsPath)
      (hsize : (H.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :=
    ComponentBudget.failure_path_leaves_large_odd_component hsmall hfailH P hp hsize
  have hpathTwoOddComponents {a b : Fin n} (P : H.Walk a b) (hp : P.IsPath)
      (hsize : (H.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :=
    ComponentDeficit.failure_path_two_odd_even_rich_components hsmall hfailH P hp hsize
  have hpathSixEven {a b : Fin n} (P : H.Walk a b) (hp : P.IsPath)
      (hsize : (H.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :=
    ComponentDeficit.failure_path_six_even_support hsmall hfailH P hp hsize
  have htwoTipsEvenCount {u v : Fin n} (huv : u ≠ v)
      (hu : Nat.card (H.neighborSet u)=2) (hv : Nat.card (H.neighborSet v)=2) :=
    TipParity.two_degree_two_implies_six_even hsmall hH hfailH huv hu hv
  have hsmallEvenTipCount (he : ComponentDeficit.evenCount H ≤ 5) :=
    TipParity.degree_two_at_most_one_of_five_even hsmall hH hfailH he
  have hpathEvenDeficit {a b : Fin n} (P : H.Walk a b) (hp : P.IsPath)
      (hsize : (H.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :=
    LowDegreeParity.failure_path_evenCount_deficit hsmall hfailH P hp hsize
  have hsmallEvenLowDegreeCount (he : ComponentDeficit.evenCount H ≤ 5) :=
    LowDegreeParity.low_degree_card_le_one_of_five_even hsmall hH hfailH he
  have hoddMinDegree (ho : Odd n) (u : Fin n) :=
    DegreeFourReduction.min_degree_five_of_odd_failure hsmall ho hH hfailH u
  have hmatchingCutParity (S : Set (Fin n))
      (hS : 3 ≤ S.ncard) (hcS : 3 ≤ Sᶜ.ncard)
      (hi : Function.Injective (BoundaryPorts.inner H S))
      (ho : Function.Injective (BoundaryPorts.outer H S)) :=
    MatchingCutMarked.failure_matching_cut_parity hsmall
      (Fintype.card_fin n) hH hfailH hS hcS hi ho
  have hoddMatchingCut (hnodd : Odd n) (S : Set (Fin n))
      (hS : S.Nonempty) (hcS : Sᶜ.Nonempty)
      (hi : Function.Injective (BoundaryPorts.inner H S))
      (ho : Function.Injective (BoundaryPorts.outer H S)) :=
    MatchingCutMarked.odd_failure_no_proper_matching_cut hsmall
      hH hnodd hfailH S hS hcS hi ho
  have hcriticalEvenIndependent
      (hf : (H.induce {v | Even (Nat.card (H.neighborSet v))}).IsAcyclic)
      {u v : Fin n} (hu : Even (Nat.card (H.neighborSet u)))
      (hv : Even (Nat.card (H.neighborSet v))) :=
    BridgeParityReduction.even_forest_independent_of_failure hsmall hH hfailH hcritical hf hu hv
  obtain ⟨a,C,hC,hCparity⟩ :=
    NonbridgeCore.exists_cycle_no_consecutive_odd hcritical hH hfailH
  have hdeletionBlocked {u v : Fin n} (h : H.Adj v u)
      (S : QuotaTrails.TrailFamily (H.deleteEdges {s(v,u)})
        ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
      (hS : ∀ i, (S.walk i).IsPath) (i)
      (hi : u=S.start i ∨ u=S.finish i) : v ∈ (S.walk i).support :=
    DeletionEndpoint.deletion_endpoint_must_meet h hfailH S hS i hi
  obtain ⟨T₁,r,hT₁eq,hroot₁,hmax₁,hqr₁,hrootDegree,hmin₁⟩ :=
    RootHighDegree.exists_small_quota_high_degree_root
      hsmall hH hfailH T₀ r₀ hscore₀ hmax₀ hroot₀
  have hscore₁ : T₁.score+1=H.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by omega
  obtain ⟨T,L,hTT₁,hquota,henergy,hroot,hrootCycleCases,hrootCycleMin,hrootTailMin⟩ :=
    TailEar.exists_shortest_rooted_structure
      hsmall hH hfailH T₁ r hscore₁ hmax₁ hroot₁ hrootDegree
  have hTeq := hTT₁.trans hT₁eq
  have hmax (U : QuotaTrails.TrailFamily H ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) :
      U.score ≤ T.score := by rw [hTT₁]; exact hmax₁ U
  have hqr : T.quota r=1 ∨ T.quota r=2 := by rw [hquota]; exact hqr₁
  have hqrle : T.quota r ≤ 2 := hqr.elim (fun h ↦ h.le.trans (by decide)) (fun h ↦ h.le)
  have hmin (U : QuotaTrails.TrailFamily H ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
      (s : Fin n) (hU : U.score=T.score) (hsRoot : QuotaRooted.HasRoot U s) :
      RootEnergy.quotaEnergy T ≤ RootEnergy.quotaEnergy U := by
    rw [henergy]
    exact hmin₁ U s (hU.trans hTT₁) hsRoot
  have hscore : T.score+1=H.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by omega
  have hdefectGroupExpansion
      (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hA : L.index ∈ A)
      (hconn : SupportConnected (MemberExpansion.selectedGraph T A))
      (hsize : (MemberExpansion.selectedGraph T A).support.ncard < n) :=
    MemberExpansion.single_defect_group_expands hsmall hfailH T hscore
      L.index L.member_not_path A hA hconn hsize
  have hnormalGroupExpansion
      (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hA : L.index ∉ A)
      (hconn : SupportConnected (MemberExpansion.selectedGraph T A)) :=
    MemberNormalExpansion.normal_group_expands hsmall hfailH T hscore
      L.index L.member_not_path A hA hconn
  have htightGroupEven
      (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hA : L.index ∉ A)
      (htight : 2*A.card=(MemberExpansion.selectedGraph T A).support.ncard+1) :=
    MemberNormalExpansion.tight_normal_group_three_even hfailH T hscore
      L.index L.member_not_path A hA htight
  have htightGroupMarked
      (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hA : L.index ∉ A)
      (hconn : SupportConnected (MemberExpansion.selectedGraph T A))
      (htight : 2*A.card=(MemberExpansion.selectedGraph T A).support.ncard+1)
      (u : Fin n) (hu : u ∈ (MemberExpansion.selectedGraph T A).support) :=
    MemberNormalExpansion.tight_normal_group_marked hsmall hfailH T hscore
      L.index L.member_not_path A hA hconn htight u hu
  have houtsideGroupExpansion
      (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊))
      (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
      (hconn : SupportConnected (MemberExpansion.selectedGraph T A))
      {x : Fin n} (hx : L.cycle.toSubgraph.Adj r x)
      (hxA : x ∈ (MemberExpansion.selectedGraph T A).support) :=
    GroupActivation.outside_group_meeting_cycle_neighbor_expands
      hsmall hfailH T hscore r L A hav hconn hx hxA
  have hsmallOutsideGroupExpansion
      (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊))
      (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
      (hconn : SupportConnected (MemberExpansion.selectedGraph T A))
      (hsize : 2*(MemberExpansion.selectedGraph T A).support.ncard < n)
      {x : Fin n} (hx : L.cycle.toSubgraph.Adj r x)
      (hxA : x ∈ (MemberExpansion.selectedGraph T A).support) :=
    LollipopGroups.small_outside_group_expands
      hsmall hfailH T hscore r L A hav hconn hsize hx hxA
  have hcycleOutsideGroupExpansion
      (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊))
      (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
      (hconn : SupportConnected (MemberExpansion.selectedGraph T A))
      (hhit : ∃ x ∈ L.cycle.support, x ∈ (MemberExpansion.selectedGraph T A).support) :=
    CyclePrefixRepair.outside_group_meeting_cycle_expands
      hsmall hfailH T hscore r L A hav hconn hhit
  have hfullyMarkedOutsideMissesCycle
      (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊))
      (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
      (hmark : ∀ x ∈ (MemberExpansion.selectedGraph T A).support,
        MarkedCycleGroups.MarkedPartition (MemberExpansion.selectedGraph T A) A.card x) :=
    CyclePrefixRepair.fully_marked_outside_group_misses_cycle
      hfailH T hscore r L A hav hmark
  have htailNotPrivate {v : Fin n} (hv : v ∈ L.tail.support)
      (hvr : v ≠ r) (hvb : v ≠ L.finish) :=
    TailEar.shortest_tail_internal_not_private
      hsmall hH hfailH T r L hscore hrootTailMin hv hvr hvb
  have hoddNormalSupport (ho : Odd n) :=
    TailEar.odd_normal_support_spanning hsmall ho hH hfailH T r L hscore hmax
  have hnormalSupportBudget :=
    NormalRemainder.normal_support_budget hsmall hH hfailH T r L hscore hmax
      hrootCycleCases hrootTailMin
  have hnormalMissingCount :=
    NormalRemainderOne.normal_support_compl_card_le_one hsmall hH hfailH T r L
      hscore hmax hrootDegree hrootCycleCases hrootTailMin
  have hleaflessNormalMissingCount (hleaf : ∀ v, Nat.card (H.neighborSet v) ≠ 1) :=
    NormalRemainder.leafless_normal_support_compl_card_le_one hsmall hH hfailH
      T r L hscore hmax hleaf hrootCycleCases hrootTailMin
  have hrootAlternatives := RootHighDegree.small_quota_high_degree_cases T r hqr hrootDegree
  have hrootLocality (i) := RootLocality.members_off_root_acyclic T r hscore hroot i
  have hrootUnique (s : Fin n) (hsRoot : QuotaRooted.HasRoot T s) :=
    RootLocality.root_unique T hscore hroot hsRoot
  have hnp : ∃ i, ¬(T.walk i).IsPath := by
    by_contra! hp
    have hh := T.score_eq_edges_add_iff.mpr hp
    omega
  have hnonempty : ∀ i, ¬(T.walk i).Nil :=
    NilSlot.max_score_nonpath_no_nil T hmax hnp
  have hbudget : Fintype.card (Fin n) ≤ 2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hc := Nat.le_ceil ((Fintype.card (Fin n) : ℚ)/2)
    exact_mod_cast (show (Fintype.card (Fin n) : ℚ) ≤
        2*(⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ : ℚ) by linarith)
  have hglobalShortestCycle :=
    RootCycleMinimum.exists_global_shortest_cycle T r hscore hroot
  have hoptimizedRootCycle (i) (C : H.Walk r r)
      (hi : (T.walk i).toSubgraph=C.toSubgraph) :=
    CarrierDeficiency.exists_optimal_with_root_deficiency T r hroot hqrle hbudget i C hi
  have hoptimizedCycleBound :=
    OutsideCarrierBudget.optimized_cycle_length_bound hsmall hH hfailH
  have hfreeCycleComponentCertificate :=
    FreeCycleChoice.exists_free_cycle_component_certificate hsmall hH hfailH hglobal T hscore r L hrootDegree
  have hjointTailCarrierCertificate :=
    JointTailCarrier.exists_joint_component_certificate hsmall hH hfailH hglobal T hscore r L
  have hfreeLollipopComponentCertificate :=
    AnchorComponentBudget.exists_optimized_lollipop_component_certificate hsmall hH hfailH T hscore r L
  have hfreeLollipopCertificate :=
    AnchorCarrier.exists_optimized_lollipop_certificate hsmall hH hfailH T hscore r L
  have hfreeCycleCertificate :=
    FreeCarrier.exists_optimized_cycle_certificate hsmall hH hfailH T hscore
  have hoptimizedCycleTwoCarriers :=
    HexagonExclusion.optimized_cycle_has_two_carriers hsmall hH hfailH T hscore hmax
  have hshortCycle (i) {a : Fin n} (C : H.Walk a a)
      (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :=
    CycleEar.exists_cycle_min_degree_three hsmall hH hfailH
      T hscore hmax hbudget i C hC hi
  have hnoTriangle (i) {a b c : Fin n} (hab : H.Adj a b)
      (hbc : H.Adj b c) (hac : H.Adj a c) :=
    TriangleAbsorption.budget_maximum_no_triangle T hH hscore hmax hbudget i hab hbc hac
  have hnoContiguousCarrier :=
    ContiguousRegion.failure_no_single_contiguous_member hsmall hH hfailH T hscore hmax
  have hnoTwoContiguous (k : ℕ) :=
    TwoCarrierRegion.failure_no_two_contiguous_members (k := k)
      hsmall (Fintype.card_fin n) hH hfailH
  have hdeletedCycleCorridor {a b c d : Fin n} :=
    CorridorReduction.deleted_cycle_corridor_budget hsmall (G := H) (r := a) (u := b) (a := c) (v := d)
  have hwholeCycleLength (i) {a : Fin n} (C : H.Walk a a)
      (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :=
    HeptagonExclusion.whole_cycle_length_ge_eight
      hsmall hH hfailH T hscore hmax i C hC hi
  have hfiveCycleIncidence (i) {a : Fin n} (C : H.Walk a a)
      (hC : C.IsCycle) (hl : C.length=5) (hi : (T.walk i).toSubgraph=C.toSubgraph)
      {u v : Fin n} (hu : u ∈ C.support) (hv : v ∈ C.support) (j) :=
    PentagonIntersection.five_cycle_equal_members T hscore hmax i C hC hl hi hu hv j
  have hcycleIntersection (i j) (hij : i ≠ j) {a : Fin n} (C : H.Walk a a)
      (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
      (hinter : ∃ x ∈ (T.walk j).support, x ∈ C.support) :=
    CycleIntersectionSeven.failure_cycle_intersection_ge_seven
      hsmall hH hfailH T hscore hmax i j hij C hC hi hinter
  have hcycleNormalSupport (i) {a : Fin n} (C : H.Walk a a)
      (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :=
    MemberComponents.cycle_normal_support_bound hsmall hH hfailH T hscore hmax i C hC hi
  have hshortestCycleComponents (i) {a : Fin n} (C : H.Walk a a)
      (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
      (hshort : CycleEar.ShortestCycle T C.length) :=
    ZeroComponentSuppression.shortest_component_count_le_two
      hsmall hH hfailH T hscore i C hC hi hshort
  have hoddWholeCycleConnectedChoice (ho : Odd n) (i) {a : Fin n} (C : H.Walk a a)
      (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :=
    ZeroComponentSuppression.exists_shortest_connected_spanning_normal
      hsmall hH hfailH T hscore i C hC hi ho
  have hcycleComponentCount (i) {a : Fin n} (C : H.Walk a a)
      (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :=
    CycleComponentBudget.normal_component_count_le_three
      hsmall hH hfailH hglobal T hscore hmax i C hC hi
  have hoddCycleComponentCount (ho : Odd n) (i) {a : Fin n} (C : H.Walk a a)
      (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :=
    CycleComponentBudget.odd_normal_component_count_le_two
      hsmall hH hfailH hglobal T hscore hmax i C hC hi ho
  have hfiveCycleSlots (i) {a : Fin n} (C : H.Walk a a)
      (hC : C.IsCycle) (hl : C.length=5) (hi : (T.walk i).toSubgraph=C.toSubgraph) :=
    CycleEndpointSlots.five_cycle_four_slots T hscore hmax hbudget i C hC hl hi
  obtain ⟨j,havoid⟩ := RootEnergy.exists_member_avoiding_small_quota_root
    T r hroot (by omega) hbudget
  obtain ⟨w,hwr,hw⟩ := RootEnergy.exists_other_surplus
    T r hscore hmax hroot (by omega) hbudget
  obtain ⟨x,y,hxy,hrx,hry,hxzero,hyzero,hxnb,hynb⟩ :=
    NonbridgeCore.two_zero_nonbridge_neighbors T r hscore hmax hroot
  have hcubicRoot (hr : Nat.card (H.neighborSet r)=3) :=
    LowDegreeAdjacency.cubic_root_two_large_zero_neighbors
      hsmall hH hfailH T r hscore hmax hroot hr
  have hcubicNormalSupport (hr : Nat.card (H.neighborSet r)=3) :=
    NormalRemainderOne.cubic_root_normal_support hsmall hH hfailH T r L hscore hmax
      hr hqrle hrootCycleCases hrootTailMin
  have hcubicRemainder (hr : Nat.card (H.neighborSet r)=3) :=
    CubicRemainder.cubic_remainder_certificate hsmall hH hfailH T r L hscore hmax
      hr hqrle hrootCycleCases hrootTailMin
  have hcubicTriangleTail (hr : Nat.card (H.neighborSet r)=3) (htri : L.cycle.length=3) :=
    TriangleTailTwo.cubic_triangle_tail_length_ge_three
      hsmall hH hfailH T r L hscore hmax hr hqrle htri
  have hcubicFreeChoice (hr : Nat.card (H.neighborSet r)=3) :=
    FreeTailGroups.cubic_free_certificate hsmall hH hfailH T r L hscore
      hr hqrle hrootCycleCases
  have hprivateFinishTail (hbr : L.finish ≠ r)
      (hb : L.finish ∉ (MemberExpansion.selectedGraph T (Finset.univ.erase L.index)).support) :=
    TerminalTail.shortest_private_finish_tail_length_one hsmall hH hfailH T r L
      hscore hmax hrootTailMin hbr hb
  have hcubicRootLeaf (hr : Nat.card (H.neighborSet r)=3) {b : Fin n}
      (hrb : H.Adj r b) (hb : Nat.card (H.neighborSet b)=1) :=
    LeafCubicEven.cubic_root_no_leaf_neighbor hsmall hH hfailH T r hscore hmax hroot hr hrb hb
  omega
end Erdos583Work
