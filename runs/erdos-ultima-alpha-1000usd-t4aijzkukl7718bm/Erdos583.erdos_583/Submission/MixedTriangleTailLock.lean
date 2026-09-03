import Submission.MixedTriangleFresh

/-! The remaining cubic/quartic short triangle has a two-edge tail whose last edge is the quartic shortcut. -/
namespace Erdos583MixedTriangleTailLockDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment Erdos583ShortTriangleSingleCarrierDevelopment
open Erdos583ShortTriangleMixedCasesDevelopment Erdos583ShortTriangleExternalCarrierDevelopment
open Erdos583ShortTriangleTailChordDevelopment Erdos583MixedTriangleFreshDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma cubic_third_neighbor {V : Type*} [Fintype V] {G : SimpleGraph V} {y r x : V}
    (hyr : G.Adj y r) (hyx : G.Adj y x) (hrx : r ≠ x) (hd : Nat.card (G.neighborSet y)=3) :
    ∃ c, G.Adj y c ∧ c ≠ r ∧ c ≠ x ∧ ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=c := by
  obtain ⟨a,b,hya,hyb,hab,har,hbr,hN⟩ := DegreeThreeReduction.degree_three_other_neighbors hyr hd
  have hx : x=a ∨ x=b := (hN x hyx).resolve_left hrx.symm
  rcases hx with hx | hx
  · subst x
    refine ⟨b,hyb,hbr,hab.symm,?_⟩
    exact hN
  · subst x
    refine ⟨a,hya,har,hab,?_⟩
    intro z hz
    rcases hN z hz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

lemma failure_mixed_short_triangle_tail_lock {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (r : Fin n) (L : RootedCycleRep T r) {x y : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hd : Nat.card (G.neighborSet r)=5)
    (hdx : Nat.card (G.neighborSet x)=4) (hdy : Nat.card (G.neighborSet y)=3) :
    L.tail.length=2 ∧ ∃ a b c, G.Adj x a ∧ G.Adj x b ∧ G.Adj y c ∧
      a ≠ b ∧ a ≠ r ∧ b ≠ r ∧ a ≠ y ∧ b ≠ y ∧ c ≠ r ∧ c ≠ x ∧
      G.Adj a b ∧ s(a,b) ∈ L.tail.edges ∧
      (∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a ∨ z=b) ∧
      (∀ z, G.Adj y z → z=r ∨ z=x ∨ z=c) := by
  classical
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  obtain ⟨hqr,hrodd,_⟩ := failure_any_short_triangle_root_degree hsmall hG hfail T hs hm r L hc (by omega)
  obtain ⟨j,hji,hrP,hunique⟩ := short_triangle_degree_five_unique_carrier T hs hm r L hc ht hqr hd
  obtain ⟨_,_,hqx,_⟩ := failure_degree_five_short_triangle_nonroot_degrees hsmall hG hfail T hs hm r L
    hrx hxy hry hC ht hd
  have hx0 : T.quota x=0 := by omega
  obtain ⟨a,b,hxa,hxb,hab,hra,hrb,hya,hyb,hNx⟩ :=
    DegreeFourReduction.degree_four_other_neighbors hrx.symm hxy hry.ne hdx
  obtain ⟨c,hyc,hcr,hcx,hNy⟩ := cubic_third_neighbor hry.symm hxy.symm hrx.ne hdy
  let C : Set (Sym2 (Fin n)) := {s(r,x),s(x,y),s(r,y)}
  let F := G.deleteEdges C
  have hCe : L.cycle.toSubgraph.edgeSet=C := by
    rw [hC]
    ext e
    simp only [C,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,
      List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  have hnxa : s(x,a) ∉ C := by simp [C,hrx.ne.symm,hxy.ne,hra.symm,hya.symm]
  have hnxb : s(x,b) ∉ C := by simp [C,hrx.ne.symm,hxy.ne,hrb.symm,hyb.symm]
  have hnyc : s(y,c) ∉ C := by simp [C,hry.ne.symm,hxy.ne.symm,hcr,hcx]
  have hxap := unique_carrier_external_edge T r L j hunique hxC hrx.ne.symm hxa (by rwa [hCe])
  have hycp := unique_carrier_external_edge T r L j hunique hyC hry.ne.symm hyc (by rwa [hCe])
  have havoid (e : Sym2 (Fin n)) (he : e ∈ C) : e ∉ (T.walk j).edges := by
    intro hep
    have hi : e ∈ (T.walk L.index).toSubgraph.edgeSet := by
      rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
      exact Or.inl (hCe.symm ▸ he)
    exact Set.disjoint_left.mp (T.disjoint hji.symm) hi ((T.walk j).mem_edges_toSubgraph.mpr hep)
  have hF : SupportConnected F := delete_triangle_connected_of_walk hG (T.walk j) hrP
    ((T.walk j).fst_mem_support_of_mem_edges hxap) ((T.walk j).fst_mem_support_of_mem_edges hycp) havoid
  have hdis : Disjoint C F.edgeSet := by
    rw [edgeSet_deleteEdges]
    exact Set.disjoint_left.mpr (fun _ he hh ↦ hh.2 he)
  have hcover : G.edgeSet=F.edgeSet ∪ C := by
    rw [edgeSet_deleteEdges]
    apply (Set.diff_union_of_subset _).symm
    rintro e (rfl|rfl|rfl)
    · exact hrx
    · exact hxy
    · exact hry
  have hNxF : ∀ z, F.Adj x z → z=a ∨ z=b := by
    intro z hz
    obtain ⟨hz,hnz⟩ := deleteEdges_adj.mp hz
    rcases hNx z hz with rfl | rfl | h | h
    · exact (hnz (Or.inl Sym2.eq_swap)).elim
    · exact (hnz (Or.inr (Or.inl rfl))).elim
    · exact Or.inl h
    · exact Or.inr h
  have hNyF : ∀ z, F.Adj y z → z=c := by
    intro z hz
    obtain ⟨hz,hnz⟩ := deleteEdges_adj.mp hz
    rcases hNy z hz with rfl | rfl | h
    · exact (hnz (Or.inr (Or.inr Sym2.eq_swap))).elim
    · exact (hnz (Or.inr (Or.inl Sym2.eq_swap))).elim
    · exact h
  have hrOddF : Odd (Nat.card (F.neighborSet r)) := by
    have hh := delete_cycle_preserves_degree_parity L.isCycle r
    rw [hCe] at hh
    change (F.neighborSet r).ncard % 2=_ at hh
    rw [Nat.odd_iff,Nat.card_coe_set_eq,hh]
    simpa only [Nat.odd_iff,Nat.card_coe_set_eq] using hrodd
  have habG : G.Adj a b := by
    by_contra hn
    exact hfail (mixed_triangle_fresh_reduction hsmall (deleteEdges_le C) hF hrx hxy hry hdis hcover
      (deleteEdges_adj.mpr ⟨hxa,hnxa⟩) (deleteEdges_adj.mpr ⟨hxb,hnxb⟩)
      (deleteEdges_adj.mpr ⟨hyc,hnyc⟩) hab hya.symm hyb.symm hcr hcx hNxF hNyF
      (fun h ↦ hn (deleteEdges_le C h)) hrOddF)
  have habT := short_triangle_external_chord_in_tail T hs hm r L hrx hxy hry hC ht hx0 j hji hunique
    hxa hxb habG hra.symm hrb.symm hya.symm hyb.symm hNx
  have hlen : L.tail.length=2 := by
    rcases ht with ht | ht
    · obtain ⟨h,hS⟩ := ShortLollipop.one_edge_form L.tail ht
      have he : s(a,b)=s(r,L.finish) := by simpa only [hS,Walk.edges_cons,Walk.edges_nil,List.mem_singleton] using habT
      have hrab : r ∈ s(a,b) := he.symm ▸ Sym2.mem_mk_left r L.finish
      simp [hra,hrb] at hrab
    · exact ht
  exact ⟨hlen,a,b,c,hxa,hxb,hyc,hab,hra.symm,hrb.symm,hya.symm,hyb.symm,hcr,hcx,habG,habT,hNx,hNy⟩

end Erdos583MixedTriangleTailLockDevelopment
