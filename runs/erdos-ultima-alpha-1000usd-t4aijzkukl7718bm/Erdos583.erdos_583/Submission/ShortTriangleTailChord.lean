import Submission.ShortTriangleEarCarrier

/-! A quartic nonroot shortcut must lie in the defective tail, not in an ordinary member. -/
namespace Erdos583ShortTriangleTailChordDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar Erdos583Work.TailEar
open Erdos583ShortTriangleEarCarrierDevelopment Erdos583ShortTriangleExternalCarrierDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma short_triangle_external_chord_in_tail {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) {x y a b : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hC : L.cycle=Walk.cons hrx (Walk.cons hxy (Walk.cons hry.symm Walk.nil)))
    (ht : L.tail.length=1 ∨ L.tail.length=2) (hqx : T.quota x=0)
    (j : Fin k) (hji : j ≠ L.index)
    (hunique : ∀ m : Fin k, m ≠ L.index →
      (∃ v ∈ L.cycle.support, v ∈ (T.walk m).support) → m=j)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : G.Adj a b)
    (har : a ≠ r) (hbr : b ≠ r) (hay : a ≠ y) (hby : b ≠ y)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a ∨ z=b) : s(a,b) ∈ L.tail.edges := by
  classical
  have hc : L.cycle.length=3 := by rw [hC]; rfl
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hxaC : s(x,a) ∉ L.cycle.toSubgraph.edgeSet := by
    rw [hC]
    simp [hrx.ne.symm,hxy.ne,har,hay]
  have hxaP := unique_carrier_external_edge T r L j hunique hxC hrx.ne.symm hxa hxaC
  have hxP : x ∈ (T.walk j).support := (T.walk j).fst_mem_support_of_mem_edges hxaP
  have hxstart : x ≠ T.start j := by
    intro he
    have hh := DeletionEndpoint.quota_pos_of_endpoint T j (Or.inl he)
    omega
  have hxfinish : x ≠ T.finish j := by
    intro he
    have hh := DeletionEndpoint.quota_pos_of_endpoint T j (Or.inr he)
    omega
  obtain ⟨u,w,A,B,hux,hxw,hform⟩ := internal_two_edge_form (T.walk j) hxP hxstart hxfinish
  have hP : (T.walk j).IsPath := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hji
  have hp : (A.append (Walk.cons hux (Walk.cons hxw B))).IsPath := hform ▸ hP
  have havoid (e : Sym2 V) (he : e ∈ L.cycle.toSubgraph.edgeSet) : e ∉ (T.walk j).edges := by
    intro hh
    have hi : e ∈ (T.walk L.index).toSubgraph.edgeSet := by
      rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
      exact Or.inl he
    exact Set.disjoint_left.mp (T.disjoint hji.symm) hi ((T.walk j).mem_edges_toSubgraph.mpr hh)
  have hxuP : s(x,u) ∈ (T.walk j).edges := by rw [hform]; simp [Sym2.eq_swap]
  have hxwP : s(x,w) ∈ (T.walk j).edges := by rw [hform]; simp
  have huxab : u=a ∨ u=b := by
    rcases hNx u hux.symm with rfl | rfl | h | h
    · exact (havoid _ (by rw [hC]; simp [Sym2.eq_swap]) hxuP).elim
    · exact (havoid _ (by rw [hC]; simp) hxuP).elim
    · exact Or.inl h
    · exact Or.inr h
  have hwxab : w=a ∨ w=b := by
    rcases hNx w hxw with rfl | rfl | h | h
    · exact (havoid _ (by rw [hC]; simp [Sym2.eq_swap]) hxwP).elim
    · exact (havoid _ (by rw [hC]; simp) hxwP).elim
    · exact Or.inl h
    · exact Or.inr h
  have huw : u ≠ w := by
    intro he
    have hh := (Walk.cons_isPath_iff hux (Walk.cons hxw B)).mp hp.of_append_right |>.2
    exact hh (List.mem_cons_of_mem _ (he.symm ▸ B.start_mem_support))
  have heuw : s(u,w)=s(a,b) := by
    rcases huxab with rfl | rfl <;> rcases hwxab with rfl | rfl
    · exact (huw rfl).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (huw rfl).elim
  have huwadj : G.Adj u w := (G.adj_congr_of_sym2 heuw).mpr hab
  obtain ⟨l,hl⟩ := (T.cover s(a,b)).mp hab
  have hli : l=L.index := by
    by_contra hn
    exact short_triangle_no_ordinary_ear_chord T hs hm r L hc ht j l hji hn hunique hxC hrx.ne.symm
      A B hux hxw huwadj hform (by rw [heuw]; exact (T.walk l).mem_edges_toSubgraph.mp hl)
  subst l
  rw [L.subgraph,Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hl
  have hnC : s(a,b) ∉ L.cycle.toSubgraph.edgeSet := by
    rw [hC]
    simp [har,hbr,hay,hby,hxa.ne.symm,hxb.ne.symm]
  exact L.tail.mem_edges_toSubgraph.mp (hl.resolve_left hnC)

end Erdos583ShortTriangleTailChordDevelopment
