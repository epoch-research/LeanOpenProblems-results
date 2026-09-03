import Submission.Work

/-! The exact endpoint-marking obstruction in the normal remainder of a
cubic rooted maximum. No general marking-flexibility assertion is assumed. -/
namespace Erdos583CubicRemainderDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MarkedCycleGroups Erdos583Work.PendantCompletion
open scoped Classical
set_option maxHeartbeats 1800000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma selected_erase_eq_delete (T : TrailFamily G k) (i : Fin k) :
    selectedGraph T (Finset.univ.erase i)=G.deleteEdges (T.walk i).toSubgraph.edgeSet := by
  classical
  ext x y
  rw [deleteEdges_adj]
  constructor
  · rintro ⟨j,hj,hxy⟩
    refine ⟨(T.walk j).toSubgraph.adj_sub hxy,?_⟩
    intro hi
    exact Set.disjoint_left.mp (T.disjoint (Finset.mem_erase.mp hj).1)
      (show s(x,y) ∈ (T.walk j).toSubgraph.edgeSet from hxy) hi
  · rintro ⟨hxy,hi⟩
    obtain ⟨j,hj⟩ := (T.cover s(x,y)).mp hxy
    have hji : j ≠ i := by rintro rfl; exact hi hj
    exact ⟨j,by simp [hji],hj⟩

lemma cycle_normal_degree_bound [Fintype V] (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hbudget : Fintype.card V ≤ 2*k)
    {x : V} (hx : x ∈ L.cycle.support) :
    Nat.card ((selectedGraph T (Finset.univ.erase L.index)).neighborSet x) < 2*(k-1) := by
  have hcycle := L.isCycle.ncard_neighborSet_toSubgraph_eq_two hx
  have hsub : L.cycle.toSubgraph.neighborSet x ⊆ (T.walk L.index).toSubgraph.neighborSet x := by
    intro y hy
    change (T.walk L.index).toSubgraph.Adj x y
    rw [L.subgraph,Walk.toSubgraph_append]
    exact Or.inl hy
  have hmem := Set.ncard_mono hsub
  rw [hcycle] at hmem
  have hsplit := ncard_neighbor_delete_subgraph_add (T.walk L.index).toSubgraph x
  rw [←selected_erase_eq_delete T L.index] at hsplit
  have hdeg : (G.neighborSet x).ncard < Fintype.card V := by
    rw [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
    exact G.degree_lt_card_verts x
  rw [Nat.card_coe_set_eq]
  have hk : 0 < k := Nat.zero_lt_of_lt L.index.isLt
  omega

lemma nonmarked_partition_even [Fintype V] {J : SimpleGraph V} {p : ℕ} {x : V}
    (hex : ∃ D : Finset J.Subgraph, GoodDecomposition J D ∧ D.card=p ∧ ∀ H ∈ D, H.edgeSet.Nonempty)
    (hmark : ¬MarkedPartition J p x) : Even (Nat.card (J.neighborSet x)) := by
  apply Nat.not_odd_iff_even.mp
  intro ho
  obtain ⟨D,hD,hcard,hne⟩ := hex
  have ho' : Odd (J.degree x) := by simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using ho
  obtain ⟨b,P,hP,hPD⟩ := MarkedBudgets.marked_of_positive_endpoint hD
    (((hD.odd_endpointMultiplicity_iff x).mpr ho').pos)
  apply hmark
  refine ⟨D,b,P,hD,hcard,hP,?_,hPD⟩
  intro hn
  obtain ⟨e,he⟩ := hne _ hPD
  simp only [Walk.mem_edges_toSubgraph,Walk.edges_eq_nil.mpr hn,List.not_mem_nil] at he

lemma cubic_neighbor_not_marked [Fintype V]
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k)
    (T : TrailFamily G k) (r : V) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k) (hd : Nat.card (G.neighborSet r)=3)
    (hq : T.quota r ≤ 2) {x : V} (hx : L.cycle.toSubgraph.Adj r x) :
    ¬MarkedPartition (selectedGraph T (Finset.univ.erase L.index)) (k-1) x := by
  classical
  have hq1 : T.quota r=1 := (QuotaParity.small_root_quota_one_iff T L.hasRoot hq).mpr (by rw [hd]; decide)
  have hh := LollipopGroups.outside_group_not_marked hfail T hs r L (Finset.univ.erase L.index)
    (fun j hj ↦ ShortLollipop.cubic_quota_one_others_avoid T r L hs hd hq1 j (Finset.mem_erase.mp hj).1) hx
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin] using hh

lemma cubic_remainder_certificate {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (r : Fin n)
    (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (hd : Nat.card (G.neighborSet r)=3) (hq : T.quota r ≤ 2)
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x))
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) :
    Even n ∧
      let J := selectedGraph T (Finset.univ.erase L.index)
      let p := ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-1
      J.support.ncard=2*p+1 ∧
      (∃ D : Finset J.Subgraph, GoodDecomposition J D ∧ D.card=p) ∧
      (∀ D : Finset J.Subgraph, GoodDecomposition J D → p ≤ D.card) ∧
      ∃ x y, x ≠ y ∧ x ∈ J.support ∧ y ∈ J.support ∧
        Even (Nat.card (J.neighborSet x)) ∧ Even (Nat.card (J.neighborSet y)) ∧
        Nat.card (J.neighborSet x) < 2*p ∧ Nat.card (J.neighborSet y) < 2*p ∧
        ¬MarkedPartition J p x ∧ ¬MarkedPartition J p y := by
  classical
  have hn : Even n := by
    apply Nat.not_odd_iff_even.mp
    intro ho
    have hh := DegreeFourReduction.min_degree_five_of_odd_failure hsmall ho hG hfail r
    omega
  have hsupport := NormalRemainderOne.cubic_root_normal_support hsmall hG hfail T r L hs hm hd hq hcases hmin
  let A := Finset.univ.erase L.index
  let J := selectedGraph T A
  let p := ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-1
  have hcardA : A.card=p := by simp [A,p]
  have hsize : J.support.ncard+1=n := by
    have hh := ({r} : Set (Fin n)).ncard_add_ncard_compl
    rw [Set.ncard_singleton,Nat.card_eq_fintype_card,Fintype.card_fin] at hh
    change (selectedGraph T (Finset.univ.erase L.index)).support.ncard+1=n
    rw [hsupport]
    omega
  have hbudget : Fintype.card (Fin n)=2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    obtain ⟨m,hmo⟩ := hn
    simp only [Fintype.card_fin,BridgeGlue.ceil_half]
    omega
  have hporder : J.support.ncard=2*p+1 := by
    have hk : 0 < ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := Nat.zero_lt_of_lt L.index.isLt
    dsimp only [p]
    have hbudget' : n=2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by simpa only [Fintype.card_fin] using hbudget
    omega
  have hia : L.index ∉ A := by simp [A]
  obtain ⟨D,hD,hDc,hDne⟩ := normal_group_exact hfail T hs L.index L.member_not_path A hia
  have hext : ∃ D : Finset J.Subgraph, GoodDecomposition J D ∧ D.card=p ∧ ∀ H ∈ D, H.edgeSet.Nonempty :=
    ⟨D,hD,hDc.trans hcardA,hDne⟩
  obtain ⟨x,y,hxy,hN⟩ := Set.ncard_eq_two.mp
    (L.isCycle.ncard_neighborSet_toSubgraph_eq_two L.cycle.start_mem_support)
  have hx : L.cycle.toSubgraph.Adj r x := by change x ∈ L.cycle.toSubgraph.neighborSet r; rw [hN]; exact Or.inl rfl
  have hy : L.cycle.toSubgraph.Adj r y := by change y ∈ L.cycle.toSubgraph.neighborSet r; rw [hN]; exact Or.inr rfl
  have hxJ : x ∈ J.support := by change x ∈ (selectedGraph T (Finset.univ.erase L.index)).support; rw [hsupport]; exact hx.ne.symm
  have hyJ : y ∈ J.support := by change y ∈ (selectedGraph T (Finset.univ.erase L.index)).support; rw [hsupport]; exact hy.ne.symm
  have hmx := cubic_neighbor_not_marked hfail T r L hs hd hq hx
  have hmy := cubic_neighbor_not_marked hfail T r L hs hd hq hy
  refine ⟨hn,hporder,⟨D,hD,hDc.trans hcardA⟩,?_,x,y,hxy,hxJ,hyJ,
    nonmarked_partition_even hext hmx,nonmarked_partition_even hext hmy,?_,?_,hmx,hmy⟩
  · intro E hE
    change p ≤ E.card
    rw [←hcardA]
    exact normal_group_cannot_save hfail T hs L.index L.member_not_path A hia E hE
  · exact cycle_normal_degree_bound T r L hbudget.le (Walk.mem_support_of_adj_toSubgraph hx.symm)
  · exact cycle_normal_degree_bound T r L hbudget.le (Walk.mem_support_of_adj_toSubgraph hy.symm)

end Erdos583CubicRemainderDevelopment
