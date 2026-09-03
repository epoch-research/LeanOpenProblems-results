import Submission.CycleGroupDisjoint

/-! Arbitrarily marked group partitions propagate across a whole cycle.
Doubling gives this flexibility for groups strictly below half the minimal
order; the equality case also uses global edge minimality. -/
namespace Erdos583MarkedCycleGroupsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open Erdos583MemberExpansionDevelopment Erdos583MemberNormalExpansionDevelopment
open Erdos583GroupActivationDevelopment Erdos583CycleGroupDisjointDevelopment
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

/-- An exact-cardinality partition with a genuine endpoint at `x`. -/
def MarkedPartition (G : SimpleGraph V) (k : ℕ) (x : V) : Prop :=
  ∃ D : Finset G.Subgraph, ∃ y, ∃ P : G.Walk x y,
    GoodDecomposition G D ∧ D.card=k ∧ P.IsPath ∧ ¬P.Nil ∧ P.toSubgraph ∈ D

lemma marked_group_cycle_closed [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i : Fin k) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (A : Finset (Fin k)) (hia : i ∉ A)
    (hmark : ∀ x ∈ (selectedGraph T A).support, MarkedPartition (selectedGraph T A) A.card x)
    {x y : V} (hxy : C.toSubgraph.Adj x y) (hx : x ∈ (selectedGraph T A).support) :
    y ∈ (selectedGraph T A).support := by
  by_contra hy
  let h := C.toSubgraph.adj_sub hxy.symm
  obtain ⟨Q,hQ,hQe⟩ := CycleFirstVisits.cycle_edge_first C hC h
    (C.mem_edges_toSubgraph.mp hxy.symm)
  obtain ⟨U,hUs,hUa,hUb,hparts,_⟩ := replace_one_general T i (Walk.cons h Q)
    hQ.isTrail (hQe.trans hi.symm)
  have hUG : selectedGraph U A=selectedGraph T A := selectedGraph_eq_of_parts T U A (fun j _ ↦ hparts j)
  have hnone : ∀ j, ¬(T.walk j).Nil := NilSlot.max_score_nonpath_no_nil T hm
    ⟨i,CycleEar.cycle_member_not_path T i C hC hi⟩
  have hav : ∀ j ∈ A, y ∉ (U.walk j).support := by
    intro j hj hyj
    apply hy
    rw [selected_support_eq T A (fun j _ ↦ hnone j)]
    refine ⟨j,hj,?_⟩
    rw [←Walk.mem_verts_toSubgraph,hparts,Walk.mem_verts_toSubgraph] at hyj
    exact hyj
  have hmU : MarkedPartition (selectedGraph U A) A.card x := by
    rw [hUG]
    exact hmark x hx
  obtain ⟨D,z,P,hD,hcard,hP,hnP,hPD⟩ := hmU
  have hnp : ¬(U.walk i).IsPath := CycleEar.cycle_member_not_path U i (Walk.cons h Q) hQ
    ((hparts i).trans (hi.trans hQe.symm))
  exact hfail (repair_with_marked_outside_group U (by omega) i hnp hUa hUb h Q hQ.isTrail
    ((hparts i).trans (hi.trans hQe.symm)) Q.end_mem_support A hia hav D hD hcard P hP hnP hPD)

lemma marked_group_cycle_subset [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i : Fin k) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (A : Finset (Fin k)) (hia : i ∉ A)
    (hmark : ∀ x ∈ (selectedGraph T A).support, MarkedPartition (selectedGraph T A) A.card x)
    (hinter : (C.toSubgraph.verts ∩ (selectedGraph T A).support).Nonempty) :
    C.toSubgraph.verts ⊆ (selectedGraph T A).support := by
  obtain ⟨x,hxC,hxA⟩ := hinter
  have transport {u v : C.toSubgraph.verts} (p : C.toSubgraph.coe.Walk u v) :
      u.val ∈ (selectedGraph T A).support → v.val ∈ (selectedGraph T A).support := by
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hu ↦ ih (marked_group_cycle_closed hfail T hs hm i C hC hi A hia hmark h hu)
  intro z hz
  obtain ⟨p⟩ := C.toSubgraph_connected ⟨x,hxC⟩ ⟨z,hz⟩
  exact transport p hxA

lemma marked_normal_group_disjoint_cycle {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i : Fin k) {a : Fin n} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (A : Finset (Fin k)) (hia : i ∉ A)
    (hc : SupportConnected (selectedGraph T A))
    (hmark : ∀ x ∈ (selectedGraph T A).support, MarkedPartition (selectedGraph T A) A.card x)
    (hsize : (selectedGraph T A).support.ncard < n)
    (hbudget : (selectedGraph T A).support.ncard ≤ 2*A.card+2) :
    Disjoint C.toSubgraph.verts (selectedGraph T A).support := by
  classical
  by_contra hn
  have hsub := marked_group_cycle_subset hfail T hs hm i C hC hi A hia hmark (Set.not_disjoint_iff.mp hn)
  let B := insert i A
  have hBA : (selectedGraph T B).support=(selectedGraph T A).support := by
    apply Set.Subset.antisymm
    · rintro x ⟨y,j,hj,hxy⟩
      rcases Finset.mem_insert.mp hj with hji|hj
      · subst j
        apply hsub
        rw [←hi]
        exact (T.walk i).toSubgraph.edge_vert hxy
      · exact ⟨y,j,hj,hxy⟩
    · exact SimpleGraph.support_mono (selectedGraph_mono T (Finset.subset_insert i A))
  have hconn : SupportConnected (selectedGraph T B) := by
    intro x hx y hy
    exact (hc x (hBA ▸ hx) y (hBA ▸ hy)).mono (selectedGraph_mono T (Finset.subset_insert i A))
  have hbound := single_defect_group_expands hsmall hfail T hs i
    (CycleEar.cycle_member_not_path T i C hC hi) B (Finset.mem_insert_self i A) hconn (by rw [hBA]; exact hsize)
  have hcB : B.card=A.card+1 := Finset.card_insert_of_notMem hia
  rw [hcB,hBA] at hbound
  omega

lemma within_support_eq (G : SimpleGraph V) : within G G.support=G := by
  ext x y
  exact ⟨fun h ↦ h.1,fun h ↦ ⟨h,G.mem_support.mpr ⟨y,h⟩,G.mem_support.mpr ⟨x,h.symm⟩⟩⟩

/-- Lift a marked support partition and use the inability to compress a normal
group to recover exact cardinality and a nonnil marked member. -/
lemma normal_group_marked_of_support [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (A : Finset (Fin k)) (hia : i ∉ A)
    {x : V} (hx : x ∈ (selectedGraph T A).support)
    (hmark : ∃ D : Finset ((selectedGraph T A).induce (selectedGraph T A).support).Subgraph,
      GoodDecomposition _ D ∧ D.card ≤ A.card ∧ MarkedDouble.MarkedAt D ⟨x,hx⟩) :
    MarkedPartition (selectedGraph T A) A.card x := by
  let J := selectedGraph T A
  obtain ⟨D,hD,hDc,a,p,hp,hm⟩ := hmark
  obtain ⟨E,q,hE,hq,hqm,hEc⟩ := MarkedBudgets.lift_induce_marked J.support hD p hp hm
  have hresult : ∃ E : Finset J.Subgraph, ∃ q : J.Walk x a.val,
      GoodDecomposition J E ∧ q.IsPath ∧ q.toSubgraph ∈ E ∧ E.card ≤ D.card := by
    have hex : ∃ E : Finset (within J J.support).Subgraph,
        ∃ q : (within J J.support).Walk x a.val,
        GoodDecomposition (within J J.support) E ∧ q.IsPath ∧ q.toSubgraph ∈ E ∧ E.card ≤ D.card :=
      ⟨E,q,hE,hq,hqm,hEc⟩
    exact Eq.mp (congrArg (fun H : SimpleGraph V ↦
      ∃ E : Finset H.Subgraph, ∃ q : H.Walk x a.val,
        GoodDecomposition H E ∧ q.IsPath ∧ q.toSubgraph ∈ E ∧ E.card ≤ D.card) (within_support_eq J)) hex
  obtain ⟨E,q,hE,hq,hqm,hEc⟩ := hresult
  have hbound := normal_group_cannot_save hfail T hs i hi A hia E hE
  have heq : E.card=A.card := by omega
  have hnonempty : q.toSubgraph.edgeSet.Nonempty := min_decomposition_edgeSet_nonempty hE
    (fun F hF ↦ heq ▸ normal_group_cannot_save hfail T hs i hi A hia F hF) hqm
  refine ⟨E,a.val,q,hE,heq,hq,?_,hqm⟩
  intro hn
  obtain ⟨e,he⟩ := hnonempty
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_eq_nil.mpr hn,List.not_mem_nil] at he

lemma small_normal_group_marked {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (A : Finset (Fin k)) (hia : i ∉ A)
    (hc : SupportConnected (selectedGraph T A))
    (hsize : 2*(selectedGraph T A).support.ncard < n)
    (hbudget : (selectedGraph T A).support.ncard ≤ 2*A.card)
    (x : Fin n) (hx : x ∈ (selectedGraph T A).support) :
    MarkedPartition (selectedGraph T A) A.card x := by
  let J := selectedGraph T A
  have hcard : Fintype.card J.support=J.support.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  apply normal_group_marked_of_support hfail T hs i hi A hia hx
  obtain ⟨D,hD,hDc,hm⟩ := MarkedDouble.marked_of_twice_order_lt hsmall
    (J.induce J.support) (hc.induce_support ⟨x,hx⟩) ⟨x,hx⟩ (by rw [hcard]; exact hsize)
  refine ⟨D,hD,?_,hm⟩
  rw [hcard,ceil_half] at hDc
  change J.support.ncard ≤ 2*A.card at hbudget
  omega

lemma half_normal_group_marked {n : ℕ} {G : SimpleGraph (Fin n)}
    (hmin : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) (hi : ¬(T.walk i).IsPath) (A : Finset (Fin k)) (hia : i ∉ A)
    (hc : SupportConnected (selectedGraph T A))
    (hsize : 2*(selectedGraph T A).support.ncard=n)
    (hedges : 2*(selectedGraph T A).edgeSet.ncard+1 < G.edgeSet.ncard)
    (hbudget : (selectedGraph T A).support.ncard ≤ 2*A.card)
    (x : Fin n) (hx : x ∈ (selectedGraph T A).support) :
    MarkedPartition (selectedGraph T A) A.card x := by
  let J := selectedGraph T A
  have hcard : Fintype.card J.support=J.support.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hecard : (J.induce J.support).edgeSet.ncard=J.edgeSet.ncard := by
    rw [←GlobalCritical.within_edge_ncard,within_support_eq]
  apply normal_group_marked_of_support hfail T hs i hi A hia hx
  obtain ⟨D,hD,hDc,hm⟩ := GlobalCritical.marked_of_half_order_fewer_edges hmin
    (J.induce J.support) (hc.induce_support ⟨x,hx⟩) ⟨x,hx⟩
    (by rw [hcard]; exact hsize) (by rw [hecard]; exact hedges)
  refine ⟨D,hD,?_,hm⟩
  rw [hcard,ceil_half] at hDc
  change J.support.ncard ≤ 2*A.card at hbudget
  omega

lemma small_normal_group_disjoint_cycle {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i : Fin k) {a : Fin n} (C : G.Walk a a) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) (A : Finset (Fin k)) (hia : i ∉ A)
    (hc : SupportConnected (selectedGraph T A))
    (hsize : 2*(selectedGraph T A).support.ncard < n)
    (hbudget : (selectedGraph T A).support.ncard ≤ 2*A.card) :
    Disjoint C.toSubgraph.verts (selectedGraph T A).support :=
  marked_normal_group_disjoint_cycle hsmall hfail T hs hm i C hC hi A hia hc
    (small_normal_group_marked hsmall hfail T hs i (CycleEar.cycle_member_not_path T i C hC hi)
      A hia hc hsize hbudget) (by omega) (by omega)

end Erdos583MarkedCycleGroupsDevelopment
