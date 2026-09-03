import Submission.Work
import Submission.HeptagonRegion

/-! The two-carrier seven-cycle core has nineteen edges: it is K₇ minus two edges. -/
namespace Erdos583HeptagonCoreDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.BridgeGlue Erdos583Work.PentagonCarriers
open Erdos583HeptagonExcursionDevelopment Erdos583HeptagonRegionDevelopment
open scoped Classical
set_option maxHeartbeats 2200000

lemma middle_adj_of_inside {V : Type*} {G : SimpleGraph V} {a b u v x y : V}
    (A : G.Walk a u) (P : G.Walk u v) (B : G.Walk v b) (S : Set V)
    (hA : ∀ z ∈ A.support, z ∈ S → z=u) (hB : ∀ z ∈ B.support, z ∈ S → z=v)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : (A.append (P.append B)).toSubgraph.Adj x y) :
    P.toSubgraph.Adj x y := by
  simp only [Walk.toSubgraph_append,Subgraph.sup_adj] at hxy
  rcases hxy with hxy|(hxy|hxy)
  · have hxu := hA x (Walk.mem_support_of_adj_toSubgraph hxy) hx
    have hyu := hA y (Walk.mem_support_of_adj_toSubgraph hxy.symm) hy
    exact ((A.toSubgraph.adj_sub hxy).ne (hxu.trans hyu.symm)).elim
  · exact hxy
  · have hxv := hB x (Walk.mem_support_of_adj_toSubgraph hxy) hx
    have hyv := hB y (Walk.mem_support_of_adj_toSubgraph hxy.symm) hy
    exact ((B.toSubgraph.adj_sub hxy).ne (hxv.trans hyv.symm)).elim

lemma two_carrier_core_ncard {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hjhit : ∃ x ∈ (T.walk j).support, x ∈ C.support)
    (hlhit : ∃ x ∈ (T.walk l).support, x ∈ C.support) :
    (within G C.toSubgraph.verts).edgeSet.ncard=19 := by
  obtain ⟨a,b,A,P,B,hj,hP,hPv,hPl,hA,hB⟩ := maximum_carrier_contiguous T hs hm i j hij C hC hl hi hjhit
  obtain ⟨c,d,D,Q,E,hl',hQ,hQv,hQl,hD,hE⟩ := maximum_carrier_contiguous T hs hm i l hil C hC hl hi hlhit
  have hother := other_members_avoid T hs hm i j l hij hil hjl C hC hl hi hjhit hlhit
  have hPe : P.toSubgraph.edgeSet ⊆ (T.walk j).toSubgraph.edgeSet := by
    rw [hj]; exact middle_edges_subset A P B
  have hQe : Q.toSubgraph.edgeSet ⊆ (T.walk l).toSubgraph.edgeSet := by
    rw [hl']; exact middle_edges_subset D Q E
  have hdCP : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    rw [←hi]; exact (T.disjoint hij).mono_right hPe
  have hdCQ : Disjoint C.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [←hi]; exact (T.disjoint hil).mono_right hQe
  have hdPQ : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet := (T.disjoint hjl).mono hPe hQe
  have heq : (within G C.toSubgraph.verts).edgeSet=
      (C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) ∪ Q.toSubgraph.edgeSet := by
    apply Set.Subset.antisymm
    · intro e he
      induction e using Sym2.ind with
      | h x y =>
        obtain ⟨hxy,hx,hy⟩ := he
        have hxC := C.mem_verts_toSubgraph.mp hx
        have hyC := C.mem_verts_toSubgraph.mp hy
        obtain ⟨q,hq⟩ := (T.cover s(x,y)).mp hxy
        by_cases hqi : q=i
        · subst q
          exact Or.inl (Or.inl (hi ▸ hq))
        · by_cases hqj : q=j
          · subst q
            rw [hj] at hq
            exact Or.inl (Or.inr (middle_adj_of_inside A P B {z | z ∈ C.support} hA hB hxC hyC hq))
          · by_cases hql : q=l
            · subst q
              rw [hl'] at hq
              exact Or.inr (middle_adj_of_inside D Q E {z | z ∈ C.support} hD hE hxC hyC hq)
            · exact (hother q hqi hqj hql x (Walk.mem_support_of_adj_toSubgraph hq) hxC).elim
    · apply Set.union_subset
      · apply Set.union_subset
        · exact subgraph_edges_within C.toSubgraph _ (Set.Subset.refl _)
        · exact subgraph_edges_within P.toSubgraph _ (by rw [hPv])
      · exact subgraph_edges_within Q.toSubgraph _ (by rw [hQv])
  rw [heq,Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hdCQ,hdPQ⟩),Set.ncard_union_eq hdCP,
    trail_edgeSet_ncard C hC.isTrail,trail_edgeSet_ncard P hP.isTrail,trail_edgeSet_ncard Q hQ.isTrail,
    hl,hPl,hQl]

lemma two_carrier_core_complement_ncard {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j l : Fin k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {r : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=7)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hjhit : ∃ x ∈ (T.walk j).support, x ∈ C.support)
    (hlhit : ∃ x ∈ (T.walk l).support, x ∈ C.support) :
    ((G.induce C.toSubgraph.verts)ᶜ).edgeSet.ncard=2 := by
  have he := two_carrier_core_ncard T hs hm i j l hij hil hjl C hC hl hi hjhit hlhit
  rw [GlobalCritical.within_edge_ncard] at he
  have hv : Fintype.card C.toSubgraph.verts=7 := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Walk.verts_toSubgraph,cycle_support_ncard hC,hl]
  have hc := edge_ncard_add_compl (G.induce C.toSubgraph.verts)
  rw [he,hv] at hc
  norm_num [Nat.choose] at hc
  omega

end Erdos583HeptagonCoreDevelopment
