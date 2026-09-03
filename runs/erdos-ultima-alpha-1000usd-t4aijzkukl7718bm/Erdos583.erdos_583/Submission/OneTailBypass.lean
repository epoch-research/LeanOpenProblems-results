import Submission.Work

/-! A one-edge tail can bypass a cross-edge on a root-avoiding ordinary path.
This is a local two-path absorption, not a full path-decomposition theorem. -/
namespace Erdos583OneTailBypassDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.TriangleAbsorption
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma one_tail_bypass_cover {r s t a b : V}
    (h : G.Adj r s) (R : G.Walk s r) (hc : (Walk.cons h R).IsCycle)
    (g : G.Adj r t) (ht : t ∉ (Walk.cons h R).support)
    (P : G.Walk a b) (hp : P.IsPath) (hr : r ∉ P.support)
    (he : s(s,t) ∈ P.edges)
    (hd : Disjoint ((Walk.cons h R).append (Walk.cons g Walk.nil)).toSubgraph.edgeSet
      P.toSubgraph.edgeSet) :
    TwoPathCover (G := G)
      (((Walk.cons h R).append (Walk.cons g Walk.nil)).toSubgraph.edgeSet ∪
        P.toSubgraph.edgeSet) := by
  have f : G.Adj s t := P.adj_of_mem_edges he
  have hst : s ≠ t := f.ne
  have hR := (Walk.cons_isCycle_iff R h).mp hc
  have htR : t ∉ R.support := fun hx ↦ ht (List.mem_cons_of_mem _ hx)
  let X := Walk.cons f.symm R
  have hX : X.IsPath := (Walk.cons_isPath_iff f.symm R).mpr ⟨hR.1,htR⟩
  obtain ⟨Q,hQ,hQe⟩ := CycleEar.path_expand_fresh_ear P hp h.symm g hst he hr
  have hXe : X.toSubgraph.edgeSet=insert s(s,t) R.toSubgraph.edgeSet := by
    ext e
    simp only [X,Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons,
      Set.mem_insert_iff,Sym2.eq_swap (a := t) (b := s)]
  have hOld : ((Walk.cons h R).append (Walk.cons g Walk.nil)).toSubgraph.edgeSet=
      R.toSubgraph.edgeSet ∪ {s(s,r),s(r,t)} := by
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,Walk.edges_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,Set.mem_union,
      Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := r) (b := s)]
    tauto
  have hsrR : s(s,r) ∉ R.toSubgraph.edgeSet := by
    simpa only [Walk.mem_edges_toSubgraph,Sym2.eq_swap (a := s) (b := r)] using hR.2
  have hrtR : s(r,t) ∉ R.toSubgraph.edgeSet := fun hx ↦
    htR (Walk.mem_support_of_adj_toSubgraph hx.symm)
  have hRP : Disjoint R.toSubgraph.edgeSet P.toSubgraph.edgeSet := by
    rw [hOld] at hd
    exact hd.mono_left Set.subset_union_left
  have hsep : Disjoint X.toSubgraph.edgeSet Q.toSubgraph.edgeSet := by
    rw [hXe,hQe]
    apply Set.disjoint_left.mpr
    intro e hx hq
    rcases hx with hx|hx
    · subst e
      rcases hq with hq|hq
      · exact hq.2 rfl
      · have hn1 : s(s,t) ≠ s(s,r) := by simp [g.ne.symm,h.ne.symm]
        have hn2 : s(s,t) ≠ s(r,t) := by simp [g.ne.symm,h.ne.symm,f.ne]
        exact (show s(s,t)=s(s,r) ∨ s(s,t)=s(r,t) from hq).elim hn1 hn2
    · rcases hq with hq|hq
      · exact Set.disjoint_left.mp hRP hx hq.1
      · rcases hq with hq|hq
        · exact hsrR (hq ▸ hx)
        · exact hrtR (hq ▸ hx)
  have hPe : s(s,t) ∈ P.toSubgraph.edgeSet := P.mem_edges_toSubgraph.mpr he
  refine ⟨t,r,a,b,X,Q,hX,hQ,hsep,?_⟩
  rw [hXe,hQe,hOld]
  ext e
  simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_diff]
  by_cases hh : e=s(s,t)
  · subst e
    simp only [hPe,eq_self,true_or,or_true]
  · tauto

lemma maximum_one_tail_cross_edge_contains_root {k : ℕ} (T : TrailFamily G k)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (r : V) (L : RootedCycleRep T r) (hl : L.tail.length=1)
    {s : V} (h : G.Adj r s) (R : G.Walk s r) (hC : L.cycle=Walk.cons h R)
    (j : Fin k) (hij : L.index ≠ j) (he : s(s,L.finish) ∈ (T.walk j).edges) :
    r ∈ (T.walk j).support := by
  by_contra hr
  obtain ⟨g,hS⟩ := ShortLollipop.one_edge_form L.tail hl
  have ht : L.finish ∉ (Walk.cons h R).support := by
    intro hx
    exact g.ne (L.inter L.finish (hC.symm ▸ hx) L.tail.end_mem_support).symm
  have hp := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  have hcover := one_tail_bypass_cover h R (hC ▸ L.isCycle) g ht (T.walk j) hp hr he
    (by rw [←hC,←hS,←L.subgraph]; exact T.disjoint hij)
  apply ShortLollipop.maximum_one_defect_no_two_path_cover T hs hm L.index j hij L.member_not_path
  simpa only [←hC,←hS,←L.subgraph] using hcover

end Erdos583OneTailBypassDevelopment
