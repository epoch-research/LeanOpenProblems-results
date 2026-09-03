import Submission.MarkedIntegrated

/-! Outside-component count in the unrestricted fixed-anchor optimization. -/
namespace Erdos583AnchorComponentBudgetDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.GroupComponents Erdos583Work.OutsideCarrierBudget
open Erdos583Work.CarrierGroups Erdos583Work.CarrierCount Erdos583Work.CarrierLength Erdos583Work.AnchorCarrier
open Erdos583Work.MarkedAbsorption Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 2200000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

noncomputable def zeroComponents (T : TrailFamily G k) (B : Finset (Fin k)) :
    Finset (inducedGraph T B).ConnectedComponent :=
  Finset.univ.filter fun D ↦
    (selectedGraph T (componentMembers T B D)).support.ncard=2*(componentMembers T B D).card

lemma component_count_budget [Fintype V] (T : TrailFamily G k) (B : Finset (Fin k))
    (hbase : ∀ D : (inducedGraph T B).ConnectedComponent,
      2*(componentMembers T B D).card ≤ (selectedGraph T (componentMembers T B D)).support.ncard) :
    2*B.card+Nat.card (inducedGraph T B).ConnectedComponent ≤
      (selectedGraph T B).support.ncard+(zeroComponents T B).card := by
  classical
  have hb (D : (inducedGraph T B).ConnectedComponent) :
      2*(componentMembers T B D).card+1 ≤
        (selectedGraph T (componentMembers T B D)).support.ncard+
          (if (selectedGraph T (componentMembers T B D)).support.ncard=
              2*(componentMembers T B D).card then 1 else 0) := by
    have hh := hbase D
    split_ifs <;> omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun D _ ↦ hb D)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  rw [sum_component_members,sum_component_support,←Finset.card_filter] at hh
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Nat.card_eq_fintype_card,
    zeroComponents] using hh

section Optimal
variable {n : ℕ} (hsmall : SmallerOrders n)
  {G : SimpleGraph (Fin n)} (hG : G.Connected)
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
    D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (K : G.Subgraph) (hnK : ¬IsPathSubgraph K) (hi : (T.walk i).toSubgraph=K)
  (hmax : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
    (U.walk i).toSubgraph=K → carrierCount U K.verts ≤ carrierCount T K.verts)
  (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score=T.score →
    (U.walk i).toSubgraph=K → carrierCount U K.verts=carrierCount T K.verts →
    carrierLength T K.verts ≤ carrierLength U K.verts)
include hsmall hG hfail hs hnK hi hmax hmin

lemma zero_outside_components_card : (zeroComponents T (outsideIndices T K.verts)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro D hD E hE
  exact zero_outside_components_unique hsmall hG hfail T hs i K hnK hi hmax hmin D E
    (Finset.mem_filter.mp hD).2 (Finset.mem_filter.mp hE).2

lemma outside_components_nontight :
    ∀ D : (inducedGraph T (outsideIndices T K.verts)).ConnectedComponent,
      2*(componentMembers T (outsideIndices T K.verts) D).card ≤
        (selectedGraph T (componentMembers T (outsideIndices T K.verts) D)).support.ncard := by
  intro D
  let B := outsideIndices T K.verts
  have hiB : i ∉ B := fun hh ↦ outside_not_touched T K.verts hh (anchor_touches T i K hnK hi)
  have hh := normal_group_expands hsmall hfail T hs i (member_not_path T i K hnK hi)
    (componentMembers T B D) (fun hh ↦ hiB (componentMembers_subset T B D hh))
    (component_support_connected T B D)
  have ht := no_tight_outside_components hsmall hG hfail T hs i K hnK hi hmax hmin
  have hne : 2*(componentMembers T B D).card ≠
      (selectedGraph T (componentMembers T B D)).support.ncard+1 := by
    intro he
    have hm : D ∈ tightComponents T B := Finset.mem_filter.mpr ⟨Finset.mem_univ D,he⟩
    rw [ht] at hm
    exact Finset.notMem_empty D hm
  change 2*(componentMembers T B D).card ≤ (selectedGraph T (componentMembers T B D)).support.ncard
  omega

lemma outside_component_budget :
    2*(outsideIndices T K.verts).card+
      Nat.card (inducedGraph T (outsideIndices T K.verts)).ConnectedComponent ≤
        (selectedGraph T (outsideIndices T K.verts)).support.ncard+1 := by
  have hb := component_count_budget T (outsideIndices T K.verts)
    (outside_components_nontight hsmall hG hfail T hs i K hnK hi hmax hmin)
  have hz := zero_outside_components_card hsmall hG hfail T hs i K hnK hi hmax hmin
  omega

lemma anchor_component_budget :
    K.verts.ncard+Nat.card (inducedGraph T (outsideIndices T K.verts)).ConnectedComponent ≤
      2*(carrierIndices T i K.verts).card+3 ∧
    (Odd n → K.verts.ncard+Nat.card (inducedGraph T (outsideIndices T K.verts)).ConnectedComponent ≤
      2*(carrierIndices T i K.verts).card+2) := by
  have hb := outside_component_budget hsmall hG hfail T hs i K hnK hi hmax hmin
  have hp := outside_carrier_partition T i K.verts (anchor_touches T i K hnK hi)
  have hv := outside_support_anchor_card T K
  simp only [Fintype.card_fin,ceil_half] at hp hv
  constructor
  · omega
  · rintro ⟨m,hm⟩
    omega

end Optimal

lemma exists_optimized_anchor_component_certificate {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (K : G.Subgraph) (hnK : ¬IsPathSubgraph K)
    (hi : (T.walk i).toSubgraph=K) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
      U.score=T.score ∧ (U.walk i).toSubgraph=K ∧
      (zeroComponents U (outsideIndices U K.verts)).card ≤ 1 ∧
      K.verts.ncard+Nat.card (inducedGraph U (outsideIndices U K.verts)).ConnectedComponent ≤
        2*(carrierIndices U i K.verts).card+3 ∧
      (Odd n → K.verts.ncard+Nat.card (inducedGraph U (outsideIndices U K.verts)).ConnectedComponent ≤
        2*(carrierIndices U i K.verts).card+2) := by
  obtain ⟨U,hUs,hUi,hmax,hmin⟩ := exists_shortest_maximum_carriers T i K hi
  have hUs' : U.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by omega
  exact ⟨U,hUs,hUi,zero_outside_components_card hsmall hG hfail U hUs' i K hnK hUi hmax hmin,
    anchor_component_budget hsmall hG hfail U hUs' i K hnK hUi hmax hmin⟩

/-- The outside components consume carrier capacity in the same optimized
family as the fixed lollipop anchor. No root-energy preservation is asserted. -/
lemma exists_optimized_lollipop_component_certificate {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : LollipopEar.RootedCycleRep T r) :
    ∃ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
      U.score=T.score ∧ (U.walk L.index).toSubgraph=(T.walk L.index).toSubgraph ∧
      (zeroComponents U (outsideIndices U (T.walk L.index).toSubgraph.verts)).card ≤ 1 ∧
      L.cycle.length+L.tail.length+
        Nat.card (inducedGraph U (outsideIndices U (T.walk L.index).toSubgraph.verts)).ConnectedComponent ≤
        2*(carrierIndices U L.index (T.walk L.index).toSubgraph.verts).card+3 ∧
      (Odd n → L.cycle.length+L.tail.length+
        Nat.card (inducedGraph U (outsideIndices U (T.walk L.index).toSubgraph.verts)).ConnectedComponent ≤
        2*(carrierIndices U L.index (T.walk L.index).toSubgraph.verts).card+2) := by
  have hnK : ¬IsPathSubgraph (T.walk L.index).toSubgraph := by
    rintro ⟨a,b,P,hP,hPe⟩
    exact L.member_not_path (ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (T.isTrail L.index) hP hPe)
  obtain ⟨U,hUs,hUi,hz,hb,ho⟩ := exists_optimized_anchor_component_certificate hsmall hG hfail T hs L.index
    (T.walk L.index).toSubgraph hnK rfl
  have hv : (T.walk L.index).toSubgraph.verts.ncard=L.cycle.length+L.tail.length := by
    rw [L.subgraph,LollipopEar.lollipop_vertex_card L.cycle L.isCycle L.tail L.isPath L.inter,Walk.length_append]
  exact ⟨U,hUs,hUi,hz,by rwa [hv] at hb,fun h ↦ by have hh := ho h; rwa [hv] at hh⟩

end Erdos583AnchorComponentBudgetDevelopment
