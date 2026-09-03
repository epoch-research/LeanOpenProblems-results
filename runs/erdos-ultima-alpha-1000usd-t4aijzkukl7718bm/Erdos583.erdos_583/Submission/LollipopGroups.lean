import Submission.Work

/-! Marked normal groups obstruct arbitrary rooted lollipops, not just whole
cycle members. Small outside groups meeting either cycle neighbor must have
strict positive support surplus. -/
namespace Erdos583LollipopGroupsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.GroupActivation Erdos583Work.MarkedCycleGroups
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

lemma outside_group_not_marked
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : V) (L : LollipopEar.RootedCycleRep T r) (A : Finset (Fin k))
    (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
    {x : V} (hx : L.cycle.toSubgraph.Adj r x) :
    ¬MarkedPartition (selectedGraph T A) A.card x := by
  rintro ⟨D,y,P,hD,hcard,hP,hnP,hPD⟩
  have hia : L.index ∉ A := by
    intro hi
    apply hav L.index hi
    exact Eq.mp (congrArg (fun v : V ↦ v ∈ (T.walk L.index).support) L.start_eq)
      (T.walk L.index).start_mem_support
  let h := L.cycle.toSubgraph.adj_sub hx
  obtain ⟨Q,hQ,hQe⟩ := CycleFirstVisits.cycle_edge_first L.cycle L.isCycle h
    (L.cycle.mem_edges_toSubgraph.mp hx)
  let p := Q.append L.tail
  have ht : (Walk.cons h p).IsTrail := by
    change ((Walk.cons h Q).append L.tail).IsTrail
    apply trail_append_of_disjoint hQ.isTrail L.isPath.isTrail
    rw [hQe]
    exact LollipopEar.edge_disjoint_of_one_common_vertex L.cycle L.tail L.inter
  have he : (T.walk L.index).toSubgraph=(Walk.cons h p).toSubgraph := by
    change (T.walk L.index).toSubgraph=((Walk.cons h Q).append L.tail).toSubgraph
    rw [L.subgraph,Walk.toSubgraph_append,Walk.toSubgraph_append,hQe]
  have hr : r ∈ p.support := by
    rw [Walk.mem_support_append_iff]
    exact Or.inl Q.end_mem_support
  exact hfail (repair_with_marked_outside_group T hs L.index L.member_not_path
    L.start_eq L.finish_eq h p ht he hr A hia hav D hD hcard P hP hnP hPD)

lemma small_outside_group_expands {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : Fin n) (L : LollipopEar.RootedCycleRep T r) (A : Finset (Fin k))
    (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
    (hc : SupportConnected (selectedGraph T A))
    (hsize : 2*(selectedGraph T A).support.ncard < n)
    {x : Fin n} (hx : L.cycle.toSubgraph.Adj r x) (hxA : x ∈ (selectedGraph T A).support) :
    2*A.card+1 ≤ (selectedGraph T A).support.ncard := by
  by_contra hn
  have hia : L.index ∉ A := by
    intro hi
    apply hav L.index hi
    exact Eq.mp (congrArg (fun v : Fin n ↦ v ∈ (T.walk L.index).support) L.start_eq)
      (T.walk L.index).start_mem_support
  exact outside_group_not_marked hfail T hs r L A hav hx
    (small_normal_group_marked hsmall hfail T hs L.index L.member_not_path A hia hc hsize (by omega) x hxA)

lemma half_outside_group_expands {n : ℕ} {G : SimpleGraph (Fin n)}
    (hmin : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : Fin n) (L : LollipopEar.RootedCycleRep T r) (A : Finset (Fin k))
    (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
    (hc : SupportConnected (selectedGraph T A))
    (hsize : 2*(selectedGraph T A).support.ncard=n)
    (hedges : 2*(selectedGraph T A).edgeSet.ncard+1 < G.edgeSet.ncard)
    {x : Fin n} (hx : L.cycle.toSubgraph.Adj r x) (hxA : x ∈ (selectedGraph T A).support) :
    2*A.card+1 ≤ (selectedGraph T A).support.ncard := by
  by_contra hn
  have hia : L.index ∉ A := by
    intro hi
    apply hav L.index hi
    exact Eq.mp (congrArg (fun v : Fin n ↦ v ∈ (T.walk L.index).support) L.start_eq)
      (T.walk L.index).start_mem_support
  exact outside_group_not_marked hfail T hs r L A hav hx
    (half_normal_group_marked hmin hfail T hs L.index L.member_not_path A hia hc hsize hedges (by omega) x hxA)

lemma saturated_outside_group_large {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : Fin n) (L : LollipopEar.RootedCycleRep T r) (A : Finset (Fin k))
    (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
    (hc : SupportConnected (selectedGraph T A))
    (hbudget : (selectedGraph T A).support.ncard ≤ 2*A.card)
    {x : Fin n} (hx : L.cycle.toSubgraph.Adj r x) (hxA : x ∈ (selectedGraph T A).support) :
    n ≤ 2*(selectedGraph T A).support.ncard := by
  by_contra hn
  have hh := small_outside_group_expands hsmall hfail T hs r L A hav hc (by omega) hx hxA
  omega

lemma saturated_half_outside_group_edge_bound {n : ℕ} {G : SimpleGraph (Fin n)}
    (hmin : GlobalCritical.MinimalEdges G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : Fin n) (L : LollipopEar.RootedCycleRep T r) (A : Finset (Fin k))
    (hav : ∀ j ∈ A, r ∉ (T.walk j).support)
    (hc : SupportConnected (selectedGraph T A))
    (hsize : 2*(selectedGraph T A).support.ncard=n)
    (hbudget : (selectedGraph T A).support.ncard ≤ 2*A.card)
    {x : Fin n} (hx : L.cycle.toSubgraph.Adj r x) (hxA : x ∈ (selectedGraph T A).support) :
    G.edgeSet.ncard ≤ 2*(selectedGraph T A).edgeSet.ncard+1 := by
  by_contra hn
  have hh := half_outside_group_expands hmin hfail T hs r L A hav hc hsize (by omega) hx hxA
  omega

omit [Fintype V] in
lemma outside_support_avoids (T : TrailFamily G k) (r : V) (A : Finset (Fin k))
    (hav : ∀ j ∈ A, r ∉ (T.walk j).support) : r ∉ (selectedGraph T A).support := by
  rintro ⟨x,j,hj,hrx⟩
  exact hav j hj (Walk.mem_support_of_adj_toSubgraph hrx)

/-- Unlike the whole-cycle case, two disjoint outside groups omit the root.
Consequently two half-order lower bounds already contradict the vertex count;
no global edge-minimality hypothesis is needed. -/
lemma disjoint_outside_groups_not_both_saturated {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (r : Fin n) (L : LollipopEar.RootedCycleRep T r) (A B : Finset (Fin k))
    (havA : ∀ j ∈ A, r ∉ (T.walk j).support)
    (havB : ∀ j ∈ B, r ∉ (T.walk j).support)
    (hcA : SupportConnected (selectedGraph T A)) (hcB : SupportConnected (selectedGraph T B))
    (hd : Disjoint (selectedGraph T A).support (selectedGraph T B).support)
    {x y : Fin n} (hx : L.cycle.toSubgraph.Adj r x) (hy : L.cycle.toSubgraph.Adj r y)
    (hxA : x ∈ (selectedGraph T A).support) (hyB : y ∈ (selectedGraph T B).support) :
    2*A.card+1 ≤ (selectedGraph T A).support.ncard ∨
      2*B.card+1 ≤ (selectedGraph T B).support.ncard := by
  by_contra! hn
  have hA := saturated_outside_group_large hsmall hfail T hs r L A havA hcA (by omega) hx hxA
  have hB := saturated_outside_group_large hsmall hfail T hs r L B havB hcB (by omega) hy hyB
  have hne : (selectedGraph T A).support ∪ (selectedGraph T B).support ≠ Set.univ := by
    intro heq
    have hr : r ∈ (selectedGraph T A).support ∪ (selectedGraph T B).support := heq.symm ▸ Set.mem_univ r
    exact hr.elim (outside_support_avoids T r A havA) (outside_support_avoids T r B havB)
  have hlt := Set.ncard_lt_card hne
  have hnat : Nat.card (Fin n)=n := by simp
  rw [Set.ncard_union_eq hd,hnat] at hlt
  omega

end Erdos583LollipopGroupsDevelopment
