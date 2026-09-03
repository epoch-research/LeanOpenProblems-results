import Submission.Work

/-! A cycle-prefix exchange with an arbitrary fully marked outside group.
The attachment to the cycle need not be adjacent to the repeated root. -/
namespace Erdos583CyclePrefixRepairDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MarkedCycleGroups Erdos583Work.LollipopEar
open scoped Classical
set_option maxHeartbeats 1800000

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

lemma cycle_prefix_exchange {r z b d : V}
    (A : G.Walk r z) (B : G.Walk z r) (S : G.Walk r b) (P : G.Walk z d)
    (hC : (A.append B).IsCycle) (hz : z ≠ r) (hS : S.IsPath) (hP : P.IsPath)
    (hCS : ∀ x ∈ (A.append B).support, x ∈ S.support → x=r)
    (hAP : ∀ x ∈ A.support, x ∈ P.support → x=z)
    (hd : Disjoint ((A.append B).append S).toSubgraph.edgeSet P.toSubgraph.edgeSet) :
    TriangleAbsorption.TwoPathCover (G := G)
      (((A.append B).append S).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  have hnA : ¬A.Nil := fun h ↦ hz h.eq.symm
  have hnB : ¬B.Nil := fun h ↦ hz h.eq
  have hA : A.IsPath := hC.isPath_of_append_left hnB
  have hB : B.IsPath := hC.isPath_of_append_right hnA
  have hBS : (B.append S).IsPath := path_append_of_support_intersection hB hS (by
    intro x hx hxS
    exact hCS x ((Walk.mem_support_append_iff _ _).mpr (Or.inr hx)) hxS)
  have hX : (A.append P).IsPath := path_append_of_support_intersection hA hP hAP
  have ht : ((A.append B).append S).IsTrail := trail_append_of_disjoint hC.isTrail hS.isTrail
    (edge_disjoint_of_one_common_vertex _ _ hCS)
  have he : (A.append P).toSubgraph.edgeSet ∪ (B.append S).toSubgraph.edgeSet =
      ((A.append B).append S).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet := by
    simp only [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    ext e
    simp only [Set.mem_union]
    tauto
  have hn : (A.append P).length+(B.append S).length =
      (((A.append B).append S).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet).ncard := by
    rw [Set.ncard_union_eq hd,trail_edgeSet_ncard _ ht,trail_edgeSet_ncard _ hP.isTrail]
    simp only [Walk.length_append]
    omega
  exact ⟨r,d,z,b,A.append P,B.append S,hX,hBS,
    TriangleAbsorption.disjoint_of_cover_length _ _ hX.isTrail hBS.isTrail _ he hn,he⟩

lemma maximum_of_one_defect_failure
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k) :
    ∀ U : TrailFamily G k, U.score ≤ T.score := by
  intro U
  have hb := U.score_le_edges_add
  have hn : U.score ≠ G.edgeSet.ncard+k := by
    intro he
    exact hfail (MatchingAppend.path_family_partition U (U.score_eq_edges_add_iff.mp he))
  omega

lemma fully_marked_outside_group_misses_cycle
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : RootedCycleRep T r) (F : Finset (Fin k))
    (hav : ∀ j ∈ F, r ∉ (T.walk j).support)
    (hmark : ∀ x ∈ (selectedGraph T F).support, MarkedPartition (selectedGraph T F) F.card x) :
    Disjoint L.cycle.toSubgraph.verts (selectedGraph T F).support := by
  classical
  apply Set.disjoint_left.mpr
  intro x hx hxF
  have hia : L.index ∉ F := by
    intro hi
    apply hav L.index hi
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  have hrF := LollipopGroups.outside_support_avoids T r F hav
  obtain ⟨z,hz,A,B,hform,hA⟩ := QuadrilateralAbsorption.first_hit_split L.cycle
    (selectedGraph T F).support ⟨x,by simpa only [Walk.mem_verts_toSubgraph] using hx,hxF⟩
  have hzr : z ≠ r := by rintro rfl; exact hrF hz
  obtain ⟨D,d,P,hD,hcard,hP,hnP,hPD⟩ := hmark z hz
  obtain ⟨U,hUs,hrest,_,_,hparts⟩ := GroupActivation.replace_path_group_tracked T F
    (fun j hj ↦ (T.one_defect_other_paths hs L.index L.member_not_path).2 j
      (fun he ↦ hia (he ▸ hj))) D hD hcard
  obtain ⟨j,hj,hUj⟩ := hparts P.toSubgraph hPD
  have hij : L.index ≠ j := fun he ↦ hia (he.symm ▸ hj)
  have hUi := (hrest L.index hia).2.2
  let Q := P.mapLe (selectedGraph_le T F)
  have hQ : Q.IsPath := hP.mapLe _
  have hQe : Q.toSubgraph=P.toSubgraph.map (Hom.ofLE (selectedGraph_le T F)) := by
    simp only [Q,Walk.mapLe,Walk.toSubgraph_map]
  have hC : (A.append B).IsCycle := hform ▸ L.isCycle
  have hCS : ∀ y ∈ (A.append B).support, y ∈ L.tail.support → y=r := by
    intro y hy ht
    exact L.inter y (hform.symm ▸ hy) ht
  have hAQ : ∀ y ∈ A.support, y ∈ Q.support → y=z := by
    intro y hy hyQ
    apply hA y hy
    apply path_support_subset_graph_support hP hnP y
    simpa only [Q,Walk.support_mapLe_eq_support] using hyQ
  have hmem : (U.walk L.index).toSubgraph=((A.append B).append L.tail).toSubgraph := by
    rw [hUi,L.subgraph,hform]
  have hd : Disjoint ((A.append B).append L.tail).toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [←hmem,←hUj.trans hQe.symm]
    exact U.disjoint hij
  have hcover := cycle_prefix_exchange A B L.tail Q hC hzr L.isPath hQ hCS hAQ hd
  have hnp : ¬(U.walk L.index).IsPath := by
    intro hp
    exact L.member_not_path (ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (T.isTrail L.index) hp hUi.symm)
  apply ShortLollipop.maximum_one_defect_no_two_path_cover U (by omega)
    (maximum_of_one_defect_failure hfail U (by omega)) L.index j hij hnp
  rw [hmem,hUj,←hQe]
  exact hcover

lemma tight_outside_group_misses_cycle {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊))
    (hav : ∀ j ∈ F, r ∉ (T.walk j).support)
    (hc : SupportConnected (selectedGraph T F))
    (htight : 2*F.card=(selectedGraph T F).support.ncard+1) :
    Disjoint L.cycle.toSubgraph.verts (selectedGraph T F).support := by
  have hia : L.index ∉ F := by
    intro hi
    apply hav L.index hi
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  apply fully_marked_outside_group_misses_cycle hfail T hs r L F hav
  intro x hx
  exact tight_normal_group_marked hsmall hfail T hs L.index L.member_not_path F hia hc htight x hx

/-- Every connected outside group meeting any cycle vertex has nonnegative
support surplus, not only groups at the two neighbors of the root. -/
lemma outside_group_meeting_cycle_expands {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (r : Fin n) (L : RootedCycleRep T r)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊))
    (hav : ∀ j ∈ F, r ∉ (T.walk j).support)
    (hc : SupportConnected (selectedGraph T F))
    (hhit : ∃ x ∈ L.cycle.support, x ∈ (selectedGraph T F).support) :
    2*F.card ≤ (selectedGraph T F).support.ncard := by
  have hia : L.index ∉ F := by
    intro hi
    apply hav L.index hi
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  have hb := normal_group_expands hsmall hfail T hs L.index L.member_not_path F hia hc
  have hne : 2*F.card ≠ (selectedGraph T F).support.ncard+1 := by
    intro he
    obtain ⟨x,hx,hxF⟩ := hhit
    exact Set.disjoint_left.mp (tight_outside_group_misses_cycle hsmall hfail T hs r L F hav hc he)
      (L.cycle.mem_verts_toSubgraph.mpr hx) hxF
  omega

lemma small_outside_group_meeting_cycle_expands {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : Fin n) (L : RootedCycleRep T r) (F : Finset (Fin k))
    (hav : ∀ j ∈ F, r ∉ (T.walk j).support)
    (hc : SupportConnected (selectedGraph T F))
    (hsize : 2*(selectedGraph T F).support.ncard < n)
    (hhit : ∃ x ∈ L.cycle.support, x ∈ (selectedGraph T F).support) :
    2*F.card+1 ≤ (selectedGraph T F).support.ncard := by
  by_contra hn
  have hia : L.index ∉ F := by
    intro hi
    apply hav L.index hi
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  have hd := fully_marked_outside_group_misses_cycle hfail T hs r L F hav
    (small_normal_group_marked hsmall hfail T hs L.index L.member_not_path F hia hc hsize (by omega))
  obtain ⟨x,hx,hxF⟩ := hhit
  exact Set.disjoint_left.mp hd (L.cycle.mem_verts_toSubgraph.mpr hx) hxF

end Erdos583CyclePrefixRepairDevelopment
