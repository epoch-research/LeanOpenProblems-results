import Submission.Work
import Submission.HeptagonCarriers

/-! The remaining seven-cycle configuration has exactly two contiguous spanning carriers. -/
namespace Erdos583HeptagonRegionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.VertexCritical
open Erdos583Work.BridgeGlue Erdos583Work.PentagonExclusion Erdos583Work.CarrierGroups
open Erdos583HeptagonCarriersDevelopment Erdos583HeptagonExcursionDevelopment
open scoped Classical
set_option maxHeartbeats 2000000

lemma failure_two_carriers {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    ∃ j l, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      (∃ x ∈ (T.walk j).support, x ∈ C.support) ∧
      (∃ x ∈ (T.walk l).support, x ∈ C.support) := by
  have hn := Set.ncard_le_card C.toSubgraph.verts
  rw [Walk.verts_toSubgraph,cycle_support_ncard hC,hl,Nat.card_fin] at hn
  have hk : 2 ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [Fintype.card_fin,ceil_half]; omega
  obtain ⟨j,hij,hhit⟩ := exists_normal_carrier T hG hk i C hi
  obtain ⟨a,b,A,P,B,hj,hP,hPv,hPl,hA,hB⟩ := maximum_carrier_contiguous T hs hm i j hij C hC hl hi hhit
  by_contra hno
  apply ContiguousRegion.failure_no_single_contiguous_member hsmall hG hfail T hs hm i j hij C hC hi A P B hj
  · intro hn
    have he := Walk.nil_iff_length_eq.mp hn
    omega
  · exact hA
  · exact hB
  · intro x hx
    rw [←Walk.mem_verts_toSubgraph,hPv] at hx
    exact C.mem_verts_toSubgraph.mp hx
  · intro l hli hlj x hx hxC
    exact hno ⟨j,l,hij,hli.symm,hlj.symm,hhit,⟨x,hx,hxC⟩⟩

lemma failure_carrier_indices_card_two {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    (carrierIndices T i C.toSubgraph.verts).card=2 := by
  have hu := carrier_indices_card_le_two T hs hm i C hC hl hi
  obtain ⟨j,l,hij,hil,hjl,hjhit,hlhit⟩ := failure_two_carriers hsmall hG hfail T hs hm i C hC hl hi
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,CycleEar.cycle_member_not_path T i C hC hi⟩
  have hmem {q} (hiq : i ≠ q) (hhit : ∃ x ∈ (T.walk q).support, x ∈ C.support) :
      q ∈ carrierIndices T i C.toSubgraph.verts := by
    obtain ⟨x,hx,hxC⟩ := hhit
    obtain ⟨y,hy⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor (T.walk q) (hn q)
      ((T.walk q).mem_verts_toSubgraph.mpr hx)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hiq.symm,x,C.mem_verts_toSubgraph.mpr hxC,y,hy⟩
  have hlo := Finset.one_lt_card_iff.mpr ⟨j,l,hmem hij hjhit,hmem hil hlhit,hjl⟩
  omega

lemma other_members_avoid {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hjhit : ∃ x ∈ (T.walk j).support, x ∈ C.support)
    (hlhit : ∃ x ∈ (T.walk l).support, x ∈ C.support) :
    ∀ q, q ≠ i → q ≠ j → q ≠ l → ∀ x ∈ (T.walk q).support, x ∉ C.support := by
  intro q hqi hqj hql x hx hxC
  exact no_three_carriers T hs hm i j l q hij hil hqi.symm hjl hqj.symm hql.symm
    C hC hl hi hjhit hlhit ⟨x,hx,hxC⟩

lemma two_carrier_degree_formula {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hjhit : ∃ x ∈ (T.walk j).support, x ∈ C.support)
    (hlhit : ∃ x ∈ (T.walk l).support, x ∈ C.support) (x : V) (hx : x ∈ C.support) :
    Nat.card (G.neighborSet x)=2+
      (if x=T.start j ∨ x=T.finish j then 1 else 2)+
      (if x=T.start l ∨ x=T.finish l then 1 else 2) := by
  have hp := (T.one_defect_other_paths hs i (CycleEar.cycle_member_not_path T i C hC hi)).2
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨i,CycleEar.cycle_member_not_path T i C hC hi⟩
  have hxj := Erdos583CycleIntersectionSevenDevelopment.maximum_heptagon_carrier_contains
    T hs hm i j hij C hC hl hi hjhit x hx
  have hxl := Erdos583CycleIntersectionSevenDevelopment.maximum_heptagon_carrier_contains
    T hs hm i l hil C hC hl hi hlhit x hx
  have hother := other_members_avoid T hs hm i j l hij hil hjl C hC hl hi hjhit hlhit
  have hN : G.neighborSet x=(C.toSubgraph.neighborSet x ∪ (T.walk j).toSubgraph.neighborSet x) ∪
      (T.walk l).toSubgraph.neighborSet x := by
    ext y
    constructor
    · intro hxy
      obtain ⟨q,hq⟩ := (T.cover s(x,y)).mp hxy
      by_cases hqi : q=i
      · subst q
        exact Or.inl (Or.inl (hi ▸ hq))
      · by_cases hqj : q=j
        · subst q; exact Or.inl (Or.inr hq)
        · by_cases hql : q=l
          · subst q; exact Or.inr hq
          · exact (hother q hqi hqj hql x (Walk.mem_support_of_adj_toSubgraph hq) hx).elim
    · intro hxy
      exact hxy.elim (fun h ↦ h.elim C.toSubgraph.adj_sub (T.walk j).toSubgraph.adj_sub)
        (T.walk l).toSubgraph.adj_sub
  have hdis {a b : Fin k} (hab : a ≠ b) :
      Disjoint ((T.walk a).toSubgraph.neighborSet x) ((T.walk b).toSubgraph.neighborSet x) := by
    apply Set.disjoint_left.mpr
    intro y hy hy'
    exact Set.disjoint_left.mp (T.disjoint hab)
      (show s(x,y) ∈ (T.walk a).toSubgraph.edgeSet from hy)
      (show s(x,y) ∈ (T.walk b).toSubgraph.edgeSet from hy')
  have hdij : Disjoint (C.toSubgraph.neighborSet x) ((T.walk j).toSubgraph.neighborSet x) := by
    rw [←hi]; exact hdis hij
  have hdil : Disjoint (C.toSubgraph.neighborSet x) ((T.walk l).toSubgraph.neighborSet x) := by
    rw [←hi]; exact hdis hil
  rw [Nat.card_coe_set_eq,hN,Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hdil,hdis hjl⟩),
    Set.ncard_union_eq hdij,hC.ncard_neighborSet_toSubgraph_eq_two hx,
    path_neighbor_ncard_formula (hp j hij.symm) (hn j),
    path_neighbor_ncard_formula (hp l hil.symm) (hn l)]
  simp only [hxj,hxl,if_true]

end Erdos583HeptagonRegionDevelopment
