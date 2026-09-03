import Submission.Work

/-! The normal remainder of a compatibly optimized rooted lollipop omits
at most two vertices, even when the defective member has an attached tail. -/
namespace Erdos583NormalRemainderDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.MemberExpansion Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma triangle_support_adj {r x y : V} (C : G.Walk r r) (hlen : C.length=3)
    (hx : x ∈ C.support) (hy : y ∈ C.support) (hne : x ≠ y) : G.Adj x y := by
  obtain ⟨a,b,hra,hab,hbr,hform⟩ := QuadrilateralAbsorption.three_cycle_rep C hlen
  simp only [hform,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
    first | exact (hne rfl).elim | exact hra | exact hra.symm | exact hab | exact hab.symm |
      exact hbr | exact hbr.symm

lemma cycle_degree_ge_two [Fintype V] {r x : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hx : x ∈ C.support) : 2 ≤ Nat.card (G.neighborSet x) := by
  have hh := Set.ncard_le_ncard (show C.toSubgraph.neighborSet x ⊆ G.neighborSet x from
    fun _ h ↦ C.toSubgraph.adj_sub h)
  rw [hC.ncard_neighborSet_toSubgraph_eq_two hx,←Nat.card_coe_set_eq] at hh
  exact hh

lemma missing_mem_removed (T : TrailFamily G k) (i : Fin k) {v : V}
    (hvG : v ∈ G.support) (hv : v ∉ (selectedGraph T (Finset.univ.erase i)).support) :
    v ∈ (T.walk i).support := by
  classical
  obtain ⟨w,hvw⟩ := G.mem_support.mp hvG
  obtain ⟨j,hj⟩ := (T.cover s(v,w)).mp hvw
  by_cases hji : j=i
  · subst j
    exact Walk.mem_support_of_adj_toSubgraph hj
  · exact (hv ⟨w,j,by simp [hji],hj⟩).elim

/-- A vertex omitted by the normal remainder has exactly one member incidence.
The no-nil conclusion from global maximality is important here. -/
lemma missing_incidence [Fintype V] (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) {v : V}
    (hvG : v ∈ G.support) (hv : v ∉ (selectedGraph T (Finset.univ.erase L.index)).support) :
    Nat.card (G.neighborSet v)+T.quota v=2+2*(if r=v then 1 else 0) := by
  classical
  have hnone := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hvi := missing_mem_removed T L.index hvG hv
  have hfilter : (Finset.univ.filter fun j ↦ v ∈ (T.walk j).support)={L.index} := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro hvj
      by_contra hji
      apply hv
      rw [selected_support_eq T _ (fun j _ ↦ hnone j)]
      exact ⟨j,by simp [hji],hvj⟩
    · rintro rfl
      exact hvi
  have hh := RootCapacity.rooted_incidence T r hs L.hasRoot v
  simpa only [hfilter,Finset.card_singleton,mul_one] using hh

lemma missing_finish_leaf [Fintype V] (T : TrailFamily G k) (r : V)
    (L : LollipopEar.RootedCycleRep T r) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hbG : L.finish ∈ G.support) (hbr : L.finish ≠ r)
    (hb : L.finish ∉ (selectedGraph T (Finset.univ.erase L.index)).support) :
    Nat.card (G.neighborSet L.finish)=1 := by
  have hh := missing_incidence T r L hs hm hbG hb
  rw [if_neg hbr.symm] at hh
  have hq := DeletionEndpoint.quota_pos_of_endpoint T L.index (Or.inr L.finish_eq.symm)
  have hpos := (Set.ncard_pos (Set.toFinite (G.neighborSet L.finish))).mpr
    (show (G.neighborSet L.finish).Nonempty from G.mem_support.mp hbG)
  rw [←Nat.card_coe_set_eq] at hpos
  omega

section Smallest
variable {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
  (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
    D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
  (T : TrailFamily G k) (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
  (hs : T.score+1=G.edgeSet.ncard+k)
  (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)

include hsmall hG hfail hs hm

lemma missing_cycle_subsingleton
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x)) :
    {v : Fin n | v ∈ L.cycle.support ∧
      v ∉ (selectedGraph T (Finset.univ.erase L.index)).support}.Subsingleton := by
  intro x hx y hy
  have hxb := TailEar.missing_normal_degree_bound T r L hs hm hx.2
  have hyb := TailEar.missing_normal_degree_bound T r L hs hm hy.2
  have hxd := cycle_degree_ge_two L.cycle L.isCycle hx.1
  have hyd := cycle_degree_ge_two L.cycle L.isCycle hy.1
  by_contra hxy
  rcases hcases with hlen|hdegree
  · have hadj := triangle_support_adj L.cycle hlen hx.1 hy.1 hxy
    by_cases hxr : x=r
    · subst x
      have hyr : y ≠ r := fun h ↦ hxy h.symm
      rw [if_neg hyr] at hyb
      have hydeg : Nat.card (G.neighborSet y)=2 := by omega
      have hlarge := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hadj.symm hydeg
      simp only [↓reduceIte] at hxb
      omega
    · rw [if_neg hxr] at hxb
      have hxdeg : Nat.card (G.neighborSet x)=2 := by omega
      have hlarge := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hadj hxdeg
      split_ifs at hyb <;> omega
  · have hx3 := hdegree x hx.1
    have hy3 := hdegree y hy.1
    have hxr : x=r := by split_ifs at hxb with h <;> omega
    have hyr : y=r := by split_ifs at hyb with h <;> omega
    exact hxy (hxr.trans hyr.symm)

lemma missing_on_cycle_or_finish
    (hmin : ∀ U : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    {v : Fin n} (hv : v ∉ (selectedGraph T (Finset.univ.erase L.index)).support) :
    v ∈ L.cycle.support ∨ v=L.finish := by
  classical
  have hn := LowDegreeAdjacency.failure_order_ge_five hG hfail
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hvG : v ∈ G.support := hG.preconnected.support_eq_univ.symm ▸ Set.mem_univ v
  have hvi := missing_mem_removed T L.index hvG hv
  rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff] at hvi
  rcases hvi with hC|hTail
  · exact Or.inl hC
  by_cases hvr : v=r
  · exact Or.inl (hvr.symm ▸ L.cycle.start_mem_support)
  by_cases hvb : v=L.finish
  · exact Or.inr hvb
  obtain ⟨j,hji,hvj⟩ := TailEar.shortest_tail_internal_not_private hsmall hG hfail T r L hs hmin hTail hvr hvb
  have hnone := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  apply False.elim
  apply hv
  rw [selected_support_eq T _ (fun j _ ↦ hnone j)]
  exact ⟨j,by simp [hji],hvj⟩

lemma normal_support_compl_card_le_two
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x))
    (hmin : ∀ U : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) :
    (selectedGraph T (Finset.univ.erase L.index)).supportᶜ.ncard ≤ 2 := by
  let A : Set (Fin n) := {v | v ∈ L.cycle.support ∧
    v ∉ (selectedGraph T (Finset.univ.erase L.index)).support}
  have hA : A.ncard ≤ 1 := Set.ncard_le_one_iff_subsingleton.mpr (missing_cycle_subsingleton hsmall hG hfail T r L hs hm hcases)
  have hsub : (selectedGraph T (Finset.univ.erase L.index)).supportᶜ ⊆ A ∪ {L.finish} := by
    intro v hv
    rcases missing_on_cycle_or_finish hsmall hG hfail T r L hs hm hmin hv with hC|hb
    · exact Or.inl ⟨hC,hv⟩
    · exact Or.inr hb
  have hle := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le A {L.finish})
  rw [Set.ncard_singleton] at hle
  omega

lemma normal_support_at_least_order_sub_two
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x))
    (hmin : ∀ U : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) :
    n ≤ (selectedGraph T (Finset.univ.erase L.index)).support.ncard+2 := by
  have hc := normal_support_compl_card_le_two hsmall hG hfail T r L hs hm hcases hmin
  have hh := (selectedGraph T (Finset.univ.erase L.index)).support.ncard_add_ncard_compl
  simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at hh
  omega

lemma leafless_normal_support_compl_card_le_one
    (hleaf : ∀ v, Nat.card (G.neighborSet v) ≠ 1)
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x))
    (hmin : ∀ U : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) :
    (selectedGraph T (Finset.univ.erase L.index)).supportᶜ.ncard ≤ 1 := by
  have hn := LowDegreeAdjacency.failure_order_ge_five hG hfail
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hsub : (selectedGraph T (Finset.univ.erase L.index)).supportᶜ ⊆
      {v | v ∈ L.cycle.support ∧ v ∉ (selectedGraph T (Finset.univ.erase L.index)).support} := by
    intro v hv
    refine ⟨?_,hv⟩
    rcases missing_on_cycle_or_finish hsmall hG hfail T r L hs hm hmin hv with hC|hb
    · exact hC
    · subst v
      by_cases hbr : L.finish=r
      · exact hbr.symm ▸ L.cycle.start_mem_support
      · exact (hleaf L.finish (missing_finish_leaf T r L hs hm
          (hG.preconnected.support_eq_univ.symm ▸ Set.mem_univ _) hbr hv)).elim
  exact (Set.ncard_le_ncard hsub).trans (Set.ncard_le_one_iff_subsingleton.mpr
    (missing_cycle_subsingleton hsmall hG hfail T r L hs hm hcases))

end Smallest

lemma normal_support_budget {n : ℕ} (hsmall : SmallerOrders n) {G : SimpleGraph (Fin n)}
    (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (r : Fin n)
    (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x))
    (hmin : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
      ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) :
    2*(⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-1) ≤
      (selectedGraph T (Finset.univ.erase L.index)).support.ncard := by
  have hbudget : ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊=(n+1)/2 := by rw [ceil_half,Fintype.card_fin]
  rcases Nat.even_or_odd n with ⟨m,hmn⟩|ho
  · have hh := normal_support_at_least_order_sub_two hsmall hG hfail T r L hs hm hcases hmin
    omega
  · have hh := TailEar.odd_normal_support_spanning hsmall ho hG hfail T r L hs hm
    rw [hh,Set.ncard_univ,Nat.card_eq_fintype_card,Fintype.card_fin]
    simp only [Fintype.card_fin] at hbudget
    omega

end Erdos583NormalRemainderDevelopment
