import Submission.DoubleSuppressionPartition

/-! Adjacent quartic true twins cannot occur in a smallest Gallai failure. -/
namespace Erdos583QuarticTwinsDevelopment
open SimpleGraph Erdos583Work Erdos583QuarticPairProxyDevelopment
open Erdos583DoubleSuppressionPartitionDevelopment Erdos583TrackedCyclePartitionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma restore_path_cover {V : Type*} {F G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) (hP : P.IsPath) (hd : Disjoint P.toSubgraph.edgeSet F.edgeSet)
    (hc : G.edgeSet=P.toSubgraph.edgeSet ∪ F.edgeSet)
    (D : Finset F.Subgraph) (hD : GoodDecomposition F D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  have he : F=G.deleteEdges P.toSubgraph.edgeSet := by
    apply SimpleGraph.edgeSet_injective
    rw [edgeSet_deleteEdges,hc]
    ext e
    constructor
    · intro h
      exact ⟨Or.inr h,fun hP ↦ Set.disjoint_left.mp hd hP h⟩
    · rintro ⟨h,hn⟩
      exact h.resolve_left hn
  subst F
  exact restore_path_subgraph ⟨_,_,P,hP,rfl⟩ hD

lemma failure_no_quartic_twins_data {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r x y a b : Fin n} (F : QuarticData G r x y a b a b) : False := by
  classical
  let E : Set (Sym2 (Fin n)) := {s(x,b),s(x,y),s(y,a),s(a,r),s(r,b)}
  let J := G.deleteEdges E
  have hxaJ : J.Adj x a := deleteEdges_adj.mpr ⟨F.xa,by
    simp [E,F.ab,F.xy.ne,F.rx.ne.symm,F.xa.ne,F.xa.ne.symm,F.xb.ne,F.ay,F.ar]⟩
  have hxrJ : J.Adj x r := deleteEdges_adj.mpr ⟨F.rx.symm,by
    simp [E,F.br.symm,F.ry.ne,F.xy.ne,F.xa.ne,F.rx.ne.symm,F.xb.ne]⟩
  have hyrJ : J.Adj y r := deleteEdges_adj.mpr ⟨F.ry.symm,by
    simp [E,F.xy.ne.symm,F.br.symm,F.ar.symm,F.ay.symm,F.ry.ne.symm,F.byy.symm,F.rx.ne]⟩
  have hybJ : J.Adj y b := deleteEdges_adj.mpr ⟨F.yd,by
    simp [E,F.xy.ne.symm,F.ab.symm,F.ay.symm,F.ry.ne.symm,F.xb.ne.symm,F.yd.ne]⟩
  let P : J.Walk a b := Walk.cons hxaJ.symm (Walk.cons hxrJ (Walk.cons hyrJ.symm (Walk.cons hybJ Walk.nil)))
  have hreach {u v : Fin n} (hu : u ∈ P.support) (hv : v ∈ P.support) : J.Reachable u v :=
    (P.takeUntil u hu).reachable.symm.trans (P.takeUntil v hv).reachable
  have hedge (u v : Fin n) (huv : G.Adj u v) : J.Reachable u v := by
    by_cases he : s(u,v) ∈ E
    · rcases he with he|he|he|he|he <;>
        rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        exact hreach (by simp [P]) (by simp [P])
    · exact (show J.Adj u v from deleteEdges_adj.mpr ⟨huv,he⟩).reachable
  have hJ : SupportConnected J := fun u _ v _ ↦ reachable_map_to_reachable id hedge (hG.preconnected u v)
  have hNx : ∀ z, J.Adj x z → z=a ∨ z=r := by
    intro z hz
    obtain ⟨hz,hn⟩ := deleteEdges_adj.mp hz
    rcases F.Nx z hz with rfl | rfl | h | rfl
    · exact Or.inr rfl
    · exact (hn (Or.inr (Or.inl rfl))).elim
    · exact Or.inl h
    · exact (hn (Or.inl rfl)).elim
  have hNy : ∀ z, J.Adj y z → z=r ∨ z=b := by
    intro z hz
    obtain ⟨hz,hn⟩ := deleteEdges_adj.mp hz
    rcases F.Ny z hz with h | rfl | rfl | h
    · exact Or.inl h
    · exact (hn (Or.inr (Or.inl Sym2.eq_swap))).elim
    · exact (hn (Or.inr (Or.inr (Or.inl rfl)))).elim
    · exact Or.inr h
  have hnar : ¬J.Adj a r := fun h ↦ (deleteEdges_adj.mp h).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hnrb : ¬J.Adj r b := fun h ↦ (deleteEdges_adj.mp h).2 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  obtain ⟨D,hD,hDc⟩ := double_suppression_partition hsmall hJ F.xy.ne hxaJ hxrJ hyrJ hybJ
    F.ar F.br.symm F.ay F.ry.ne hNx hNy hnar hnrb (by simp [F.ar,F.ab])
  have patch {u v : Fin n} (Q : G.Walk u v)
      (hsub : ∀ e ∈ Q.edges, e ∈ E)
      (hfull : ∀ e ∈ E, e ∈ G.edgeSet → e ∈ Q.edges) :
      Disjoint Q.toSubgraph.edgeSet J.edgeSet ∧ G.edgeSet=Q.toSubgraph.edgeSet ∪ J.edgeSet := by
    refine ⟨Set.disjoint_left.mpr (fun e he hJ ↦ (show e ∈ G.edgeSet \ E from
      (edgeSet_deleteEdges (G := G) (s := E)) ▸ hJ).2 (hsub e (Q.mem_edges_toSubgraph.mp he))),?_⟩
    rw [edgeSet_deleteEdges]
    ext e
    constructor
    · intro he
      by_cases hh : e ∈ E
      · exact Or.inl (Q.mem_edges_toSubgraph.mpr (hfull e hh he))
      · exact Or.inr ⟨he,hh⟩
    · rintro (he|he)
      · exact Q.toSubgraph.edgeSet_subset he
      · exact he.1
  have finish {u v : Fin n} (Q : G.Walk u v) (hQ : Q.IsPath)
      (hsub : ∀ e ∈ Q.edges, e ∈ E)
      (hfull : ∀ e ∈ E, e ∈ G.edgeSet → e ∈ Q.edges) : False := by
    obtain ⟨hd,hc⟩ := patch Q hsub hfull
    obtain ⟨L,hL,hLc⟩ := restore_path_cover Q hQ hd hc D hD
    exact hfail ⟨L,hL,hLc.trans hDc⟩
  by_cases har : G.Adj a r
  · by_cases hrb : G.Adj r b
    · let Q := Walk.cons F.xb.symm (Walk.cons F.xy (Walk.cons F.yc (Walk.cons har (Walk.cons hrb Walk.nil))))
      have hQ : Q.IsCycle := by
        have hrx := F.rx.ne
        have hry := F.ry.ne
        have hxy := F.xy.ne
        have hxa := F.xa.ne
        have hxb := F.xb.ne
        have hya := F.yc.ne
        have hyb := F.yd.ne
        have hA := F.ar
        have hB := F.br
        have hAB := F.ab
        simp only [Q,Walk.cons_isCycle_iff,Walk.isPath_def,Walk.support_cons,Walk.support_nil,
          List.nodup_cons,List.nodup_nil,and_true,List.mem_cons,List.not_mem_nil,or_false,not_or,
          Walk.edges_cons,Walk.edges_nil]
        simp only [not_or,Sym2.eq_iff,not_and_or]
        aesop
      obtain ⟨hd,hc⟩ := patch Q (by
        intro e he
        simpa [Q,E,Sym2.eq_swap (a := b) (b := x)] using he) (by
        intro e he _
        simpa [Q,E,Sym2.eq_swap (a := b) (b := x)] using he)
      exact failure_no_pentagon_partition hsmall hG hfail (deleteEdges_le E) Q hQ rfl hd hc D hD hDc
    · let Q := Walk.cons F.xb.symm (Walk.cons F.xy (Walk.cons F.yc (Walk.cons har Walk.nil)))
      have hQ : Q.IsPath := by
        apply Walk.IsPath.mk'
        simp [Q,Walk.support,F.xb.ne.symm,F.byy,F.ab.symm,F.br,F.xy.ne,F.xa.ne,F.rx.ne.symm,F.yc.ne,F.ry.ne.symm,F.ar]
      apply finish Q hQ
      · intro e he
        simp only [Q,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl|rfl|rfl|rfl <;> simp [E,Sym2.eq_swap]
      · rintro e (rfl|rfl|rfl|rfl|rfl) he
        · simp [Q,Sym2.eq_swap]
        · simp [Q]
        · simp [Q]
        · simp [Q]
        · exact (hrb he).elim
  · by_cases hrb : G.Adj r b
    · let Q := Walk.cons hrb (Walk.cons F.xb.symm (Walk.cons F.xy (Walk.cons F.yc Walk.nil)))
      have hQ : Q.IsPath := by
        apply Walk.IsPath.mk'
        simp [Q,Walk.support,F.br.symm,F.rx.ne,F.ry.ne,F.ar.symm,F.xb.ne.symm,F.byy,F.ab.symm,F.xy.ne,F.xa.ne,F.yc.ne]
      apply finish Q hQ
      · intro e he
        simp only [Q,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl|rfl|rfl|rfl <;> simp [E,Sym2.eq_swap]
      · rintro e (rfl|rfl|rfl|rfl|rfl) he
        · simp [Q,Sym2.eq_swap]
        · simp [Q]
        · simp [Q]
        · exact (har he).elim
        · simp [Q]
    · let Q := Walk.cons F.xb.symm (Walk.cons F.xy (Walk.cons F.yc Walk.nil))
      have hQ : Q.IsPath := by
        apply Walk.IsPath.mk'
        simp [Q,Walk.support,F.xb.ne.symm,F.byy,F.ab.symm,F.xy.ne,F.xa.ne,F.yc.ne]
      apply finish Q hQ
      · intro e he
        simp only [Q,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl|rfl|rfl <;> simp [E,Sym2.eq_swap]
      · rintro e (rfl|rfl|rfl|rfl|rfl) he
        · simp [Q,Sym2.eq_swap]
        · simp [Q]
        · simp [Q]
        · exact (har he).elim
        · exact (hrb he).elim

end Erdos583QuarticTwinsDevelopment
