import Submission.Work
import Submission.PentagonCarriers
import Submission.OddContiguousRegion

/-! Whole pentagons are excluded from smallest-order failures. -/
namespace Erdos583PentagonExclusionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.QuotaTrails Erdos583Work.VertexCritical
open Erdos583Work.BridgeGlue
open Erdos583PentagonCarriersDevelopment Erdos583PentagonExcursionDevelopment
open Erdos583OddContiguousRegionDevelopment
open scoped Classical
set_option maxHeartbeats 1800000

lemma exists_normal_carrier {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hG : G.Connected) (hk : 2 ≤ k)
    (i : Fin k) {r : V} (C : G.Walk r r)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    ∃ j, i ≠ j ∧ ∃ x ∈ (T.walk j).support, x ∈ C.support := by
  by_contra hno
  push_neg at hno
  have hS : {x | x ∈ C.support}=Set.univ := by
    apply TrailBudget.connected_closed_set hG _ ⟨r,C.start_mem_support⟩
    intro x y hxy hx
    obtain ⟨j,hj⟩ := (T.cover s(x,y)).mp hxy
    by_cases he : i=j
    · subst j
      rw [hi] at hj
      exact Walk.mem_support_of_adj_toSubgraph (C.toSubgraph.symm hj)
    · exact (hno j he x (Walk.mem_support_of_adj_toSubgraph hj) hx).elim
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j,hji⟩ := exists_ne i
  exact hno j hji.symm (T.start j) (T.walk j).start_mem_support (by
    change T.start j ∈ {x | x ∈ C.support}
    rw [hS]; trivial)

lemma failure_no_whole_pentagon {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=5)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) : False := by
  have hb : Fintype.card (Fin n) ≤ 2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [Fintype.card_fin,ceil_half]; omega
  have hk := CycleEndpointSlots.five_cycle_four_slots T hs hm hb i C hC hl hi
  have hn : 7 ≤ n := by simp only [Fintype.card_fin,ceil_half] at hk; omega
  obtain ⟨j,hij,hhit⟩ := exists_normal_carrier T hG (by omega) i C hi
  obtain ⟨a,b,A,P,B,hj,hP,hPv,_,hA,hB⟩ := maximum_carrier_contiguous T hs hm i j hij C hC hl hi hhit
  have hother (l) (hli : l ≠ i) (hlj : l ≠ j) (x) (hx : x ∈ (T.walk l).support) : x ∉ C.support := by
    intro hxC
    exact hlj (carrier_unique T hs hm i l j hli.symm hij C hC hl hi ⟨x,hx,hxC⟩ hhit)
  have hpj := (T.one_defect_other_paths hs i (CycleEar.cycle_member_not_path T i C hC hi)).2 j hij.symm
  apply failure_no_contiguous_region hsmall hG hfail C hC (by omega) (by rw [hl]; decide)
    (by omega) A P B (hj ▸ hpj) hA hB
  · intro x hx
    rw [←Walk.mem_verts_toSubgraph,hPv] at hx
    exact C.mem_verts_toSubgraph.mp hx
  · rw [←hj,←hi]
    exact T.disjoint hij.symm
  · intro x hx y hxy
    obtain ⟨l,he⟩ := (T.cover s(x,y)).mp hxy
    by_cases hli : l=i
    · subst l
      exact Or.inl (hi ▸ he)
    · by_cases hlj : l=j
      · subst l
        exact Or.inr ((congrArg Walk.toSubgraph hj) ▸ he)
      · exact (hother l hli hlj x (Walk.mem_support_of_adj_toSubgraph he) hx).elim

lemma whole_cycle_length_ge_six {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {r : Fin n}
    (C : G.Walk r r) (hC : C.IsCycle) (hi : (T.walk i).toSubgraph=C.toSubgraph) :
    6 ≤ C.length := by
  have hb : Fintype.card (Fin n) ≤ 2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [Fintype.card_fin,ceil_half]; omega
  have hl := QuadrilateralAbsorption.whole_cycle_length_ge_five T hG hs hm hb i C hC hi
  have hne : C.length ≠ 5 := fun he ↦ failure_no_whole_pentagon hsmall hG hfail T hs hm i C hC he hi
  omega

end Erdos583PentagonExclusionDevelopment
