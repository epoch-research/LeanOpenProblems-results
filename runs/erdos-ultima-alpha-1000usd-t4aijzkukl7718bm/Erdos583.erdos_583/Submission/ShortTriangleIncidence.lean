import Submission.ShortTriangleBounds

/-! Incidence dominance and degree bounds for any short triangular defect.
A triangle is automatically a globally shortest cycle; no extra optimization is needed. -/
namespace Erdos583ShortTriangleIncidenceDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleBoundsDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma triangle_is_unrestricted_minimum {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3) :
    ∀ W : TrailFamily G k, ∀ u : V, ∀ M : RootedCycleRep W u,
      W.score=T.score → L.cycle.length ≤ M.cycle.length := by
  intro W u M _
  rw [hc]
  exact M.isCycle.three_le_length

lemma failure_any_short_triangle_root_degree {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) (hc : L.cycle.length=3) (ht : L.tail.length ≤ 2) :
    T.quota r=1 ∧ Odd (Nat.card (G.neighborSet r)) ∧ 5 ≤ Nat.card (G.neighborSet r) :=
  failure_short_triangle_root_degree hsmall hG hfail T hs hm r L
    (triangle_is_unrestricted_minimum T r L hc) hc ht

lemma short_triangle_member_contains_root {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2) (j : Fin k)
    {v : V} (hvC : v ∈ L.cycle.support) (hvj : v ∈ (T.walk j).support) : r ∈ (T.walk j).support := by
  by_cases hji : j=L.index
  · subst j
    rw [←Walk.mem_verts_toSubgraph,L.subgraph,Walk.mem_verts_toSubgraph,Walk.mem_support_append_iff]
    exact Or.inl L.cycle.start_mem_support
  · by_contra hrj
    rcases ht with ht | ht
    · exact ShortLollipop.maximum_short_triangle_no_outside_intersection T r L hs hm hc ht j (Ne.symm hji) hrj ⟨v,hvC,hvj⟩
    · exact TriangleTailTwo.maximum_two_tail_triangle_no_outside_intersection T r L hs hm hc ht j (Ne.symm hji) hrj ⟨v,hvC,hvj⟩

lemma rooted_support_degree_dominance {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k) (hr : HasRoot T r)
    {v : V} (hvr : v ≠ r) (hdom : ∀ j, v ∈ (T.walk j).support → r ∈ (T.walk j).support) :
    Nat.card (G.neighborSet v)+T.quota v+2 ≤ Nat.card (G.neighborSet r)+T.quota r := by
  classical
  have hc : (Finset.univ.filter fun j ↦ v ∈ (T.walk j).support).card ≤
      (Finset.univ.filter fun j ↦ r ∈ (T.walk j).support).card :=
    Finset.card_le_card (by intro j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,hdom j (Finset.mem_filter.mp hj).2⟩)
  have hv := RootCapacity.rooted_incidence T r hs hr v
  have hh := RootCapacity.rooted_incidence T r hs hr r
  simp only [if_neg hvr.symm,↓reduceIte,mul_zero,mul_one,add_zero] at hv hh
  omega

lemma failure_short_triangle_other_cycle_degree {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2) {v : Fin n}
    (hvC : v ∈ L.cycle.support) (hvr : v ≠ r) :
    Nat.card (G.neighborSet v)+T.quota v+1 ≤ Nat.card (G.neighborSet r) := by
  have hq := (failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc (by omega)).1
  have hh := rooted_support_degree_dominance T r hs L.hasRoot hvr
    (fun j hj ↦ short_triangle_member_contains_root T hs hm r L hc ht j hvC hj)
  omega

lemma odd_failure_short_triangle_root_degree_ge_seven {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Odd n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) (hc : L.cycle.length=3) (ht : L.tail.length ≤ 2) :
    7 ≤ Nat.card (G.neighborSet r) := by
  have hmins := triangle_is_unrestricted_minimum T r L hc
  have hb : Fintype.card (Fin n) ≤ 2*⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simp only [Fintype.card_fin,BridgeGlue.ceil_half]; omega
  have hnL := Erdos583FreeRootWholeCycleExclusionDevelopment.unrestricted_minimum_tail_not_nil hG
    (Erdos583UnrestrictedDefectCertificateDevelopment.rooted_cycle_budget_ge_two T r L hb) T hs hm r L hmins
  have hpos := Walk.not_nil_iff_lt_length.mp hnL
  have hvC : L.cycle.snd ∈ L.cycle.support :=
    Walk.mem_support_of_adj_toSubgraph (L.cycle.toSubgraph_adj_snd L.isCycle.not_nil).symm
  have hvr : L.cycle.snd ≠ r := (L.cycle.adj_snd L.isCycle.not_nil).ne.symm
  have hlow := DegreeFourReduction.min_degree_five_of_odd_failure hsmall hn hG hfail L.cycle.snd
  have hbound := failure_short_triangle_other_cycle_degree hsmall hG hfail T hs hm r L hc (by omega) hvC hvr
  obtain ⟨m,hm⟩ := (failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc ht).2.1
  omega

lemma short_triangle_carrier_degree_identity {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hc : L.cycle.length=3)
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hq : T.quota r=1) :
    Nat.card (G.neighborSet r)=
      2*(Finset.univ.filter fun j ↦ ∃ v ∈ L.cycle.support, v ∈ (T.walk j).support).card+1 := by
  classical
  have he : (Finset.univ.filter fun j ↦ ∃ v ∈ L.cycle.support, v ∈ (T.walk j).support)=
      (Finset.univ.filter fun j ↦ r ∈ (T.walk j).support) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨v,hv,hj⟩
      exact short_triangle_member_contains_root T hs hm r L hc ht j hv hj
    · exact fun hj ↦ ⟨r,L.cycle.start_mem_support,hj⟩
  rw [he]
  have hh := RootCapacity.rooted_incidence T r hs L.hasRoot r
  simp only [↓reduceIte,mul_one,hq] at hh
  omega

end Erdos583ShortTriangleIncidenceDevelopment
