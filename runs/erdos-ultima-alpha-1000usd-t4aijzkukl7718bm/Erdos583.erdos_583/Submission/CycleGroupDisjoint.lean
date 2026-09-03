import Submission.GroupActivation

/-! Tight normal groups cannot meet a whole cycle member in a smallest-order
failure. This statement does not apply to an arbitrary attached lollipop. -/
namespace Erdos583CycleGroupDisjointDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.VertexCritical
open Erdos583Work.BridgeGlue
open Erdos583MemberExpansionDevelopment Erdos583MemberNormalExpansionDevelopment
open Erdos583GroupActivationDevelopment
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma selectedGraph_eq_of_parts (T U : TrailFamily G k) (A : Finset (Fin k))
    (he : ∀ i ∈ A, (U.walk i).toSubgraph=(T.walk i).toSubgraph) :
    selectedGraph U A=selectedGraph T A := by
  ext x y
  constructor <;> rintro ⟨i,hi,hxy⟩
  · exact ⟨i,hi,by rwa [he i hi] at hxy⟩
  · exact ⟨i,hi,by rwa [he i hi]⟩

lemma selectedGraph_mono (T : TrailFamily G k) {A B : Finset (Fin k)} (hAB : A ⊆ B) :
    selectedGraph T A ≤ selectedGraph T B := by
  rintro x y ⟨i,hi,hxy⟩
  exact ⟨i,hAB hi,hxy⟩

lemma tight_group_cycle_closed {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n}
    (C : G.Walk a a) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (_hia : i ∉ A)
    (hc : SupportConnected (selectedGraph T A))
    (htight : 2*A.card=(selectedGraph T A).support.ncard+1)
    {x y : Fin n} (hxy : C.toSubgraph.Adj x y) (hx : x ∈ (selectedGraph T A).support) :
    y ∈ (selectedGraph T A).support := by
  by_contra hy
  have hyC : y ∈ C.support := Walk.mem_support_of_adj_toSubgraph hxy.symm
  let E := C.rotate hyC
  have hE : E.IsCycle := hC.rotate hyC
  have hEe : E.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hyC
  obtain ⟨U,hUs,hUa,hUb,hparts,_⟩ := replace_one_general T i E hE.isTrail (hEe.trans hi.symm)
  have hcycle : (U.walk i).toSubgraph=(E.append Walk.nil).toSubgraph := by
    rw [Walk.append_nil,hparts i,hi,hEe]
  let L : LollipopEar.RootedCycleRep U y :=
    ⟨i,y,hUa,hUb,E,Walk.nil,hE,Walk.IsPath.nil,
      (by intro z _ hz; simpa only [Walk.support_nil,List.mem_singleton] using hz),hcycle⟩
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
  have hxc : L.cycle.toSubgraph.Adj y x := by
    change E.toSubgraph.Adj y x
    rw [hEe]
    exact hxy.symm
  have hh := rooted_cycle_tight_group_avoids_neighbors hsmall hfail U (by omega) y L A hav
    (by rw [hUG]; exact hc) (by rw [hUG]; exact htight) hxc
  exact hh (by rw [hUG]; exact hx)

lemma tight_group_cycle_subset {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n}
    (C : G.Walk a a) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hia : i ∉ A)
    (hc : SupportConnected (selectedGraph T A))
    (htight : 2*A.card=(selectedGraph T A).support.ncard+1)
    (hinter : (C.toSubgraph.verts ∩ (selectedGraph T A).support).Nonempty) :
    C.toSubgraph.verts ⊆ (selectedGraph T A).support := by
  obtain ⟨x,hxC,hxA⟩ := hinter
  have transport {u v : C.toSubgraph.verts} (p : C.toSubgraph.coe.Walk u v) :
      u.val ∈ (selectedGraph T A).support → v.val ∈ (selectedGraph T A).support := by
    induction p with
    | nil => exact id
    | cons h p ih =>
      exact fun hu ↦ ih (tight_group_cycle_closed hsmall hfail T hs hm i C hC hi A hia hc htight h hu)
  intro z hz
  obtain ⟨p⟩ := C.toSubgraph_connected ⟨x,hxC⟩ ⟨z,hz⟩
  exact transport p hxA

lemma tight_normal_group_disjoint_cycle {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n}
    (C : G.Walk a a) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (A : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hia : i ∉ A)
    (hc : SupportConnected (selectedGraph T A))
    (htight : 2*A.card=(selectedGraph T A).support.ncard+1) :
    Disjoint C.toSubgraph.verts (selectedGraph T A).support := by
  classical
  by_contra hn
  have hinter : (C.toSubgraph.verts ∩ (selectedGraph T A).support).Nonempty :=
    Set.not_disjoint_iff.mp hn
  have hsub := tight_group_cycle_subset hsmall hfail T hs hm i C hC hi A hia hc htight hinter
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
  have hA : A.card < ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ A,fun h ↦ hia (h.symm ▸ Finset.mem_univ i)⟩)
    simpa only [Finset.card_univ,Fintype.card_fin] using hlt
  have hsize : (selectedGraph T B).support.ncard < n := by
    rw [hBA]
    simp only [Fintype.card_fin,ceil_half] at hA
    omega
  have hbound := single_defect_group_expands hsmall hfail T hs i
    (CycleEar.cycle_member_not_path T i C hC hi) B (Finset.mem_insert_self i A) hconn hsize
  have hcB : B.card=A.card+1 := Finset.card_insert_of_notMem hia
  rw [hcB,hBA] at hbound
  omega

end Erdos583CycleGroupDisjointDevelopment
