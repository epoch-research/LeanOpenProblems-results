import Submission.QuarticPairProxy

/-! Two present cross-edges absorb a quartic pair using one extra path. -/
namespace Erdos583QuarticPairCrossDevelopment
open SimpleGraph Erdos583Work Erdos583PrivateProxyDevelopment
open Erdos583QuarticPairProxyDevelopment Erdos583PunctureConnectivityDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma QuarticData.both_cross_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} {r x y a b c d : Fin n}
    (F : QuarticData G r x y a b c d)
    (hKconn : SupportConnected (puncture G ({x,y} : Set (Fin n))))
    (hab : G.Adj a b) (hcd : G.Adj c d) (hac : G.Adj a c) (hbd : G.Adj b d)
    (had : a ≠ d) (hbc : b ≠ c) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {x,y}
  let K := puncture G S
  let H := K.deleteEdges {s(a,b)}
  have hxH : x ∉ H.support := by
    rintro ⟨v,hv⟩
    exact (deleteEdges_adj.mp hv).1.2.1 (Or.inl rfl)
  have hyH : y ∉ H.support := by
    rintro ⟨v,hv⟩
    exact (deleteEdges_adj.mp hv).1.2.1 (Or.inr rfl)
  have hacH : H.Adj a c := deleteEdges_adj.mpr
    ⟨⟨hac,by simp [S,F.xa.ne.symm,F.ay],by simp [S,F.cx,F.yc.ne.symm]⟩,by simp [hbc.symm,F.ab]⟩
  have hcdH : H.Adj c d := deleteEdges_adj.mpr
    ⟨⟨hcd,by simp [S,F.cx,F.yc.ne.symm],by simp [S,F.dx,F.yd.ne.symm]⟩,by simp [hac.ne.symm,hbc.symm]⟩
  have hbdH : H.Adj b d := deleteEdges_adj.mpr
    ⟨⟨hbd,by simp [S,F.xb.ne.symm,F.byy],by simp [S,F.dx,F.yd.ne.symm]⟩,by simp [F.ab.symm,had.symm]⟩
  have hH : SupportConnected H := supported_delete_edge_connected hKconn
    (hacH.reachable.trans (hcdH.reachable.trans hbdH.reachable.symm))
  apply gallai_private_pair_proxy hsmall G H F.xy.ne hH hxH hyH
  intro D hD
  let P := Walk.cons F.xa.symm (Walk.cons F.xy (Walk.cons F.yc Walk.nil))
  let Q0 := Walk.cons F.xb.symm (Walk.cons F.rx.symm (Walk.cons F.ry (Walk.cons F.yd Walk.nil)))
  let Q := Walk.cons hac.symm (Walk.cons hab Q0)
  have hP : P.IsPath := by
    apply Walk.IsPath.mk'
    simp [P,Walk.support,F.xa.ne.symm,F.ay,hac.ne,F.xy.ne,F.cx.symm,F.yc.ne]
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    simp [Q,Q0,Walk.support,hac.ne.symm,hbc.symm,F.cx,F.cr,F.yc.ne.symm,F.cd,
      F.ab,F.xa.ne.symm,F.ar,F.ay,had,F.xb.ne.symm,F.br,F.byy,hbd.ne,
      F.rx.ne.symm,F.xy.ne,F.dx.symm,F.ry.ne,F.dr.symm,F.yd.ne]
  have htouch : ∀ e ∈ Q0.edges, ∃ z ∈ S, z ∈ e := by
    intro e he
    simp only [Q0,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_right _ _⟩
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_left _ _⟩
    · exact ⟨y,Or.inr rfl,Sym2.mem_mk_right _ _⟩
    · exact ⟨y,Or.inr rfl,Sym2.mem_mk_left _ _⟩
  have hQ0K := puncture_disjoint_walk S Q0 htouch
  have hcover0 : G.edgeSet=K.edgeSet ∪ P.toSubgraph.edgeSet ∪ Q0.toSubgraph.edgeSet :=
    puncture_two_walks_cover S P Q0 (by
      rintro z (rfl|rfl) v hv
      · rcases F.Nx v hv with rfl | rfl | rfl | rfl <;> simp [P,Q0,Sym2.eq_swap]
      · rcases F.Ny v hv with rfl | rfl | rfl | rfl <;> simp [P,Q0,Sym2.eq_swap])
  have hQe : Q.toSubgraph.edgeSet={s(a,c),s(a,b)} ∪ Q0.toSubgraph.edgeSet := by
    ext e
    simp [Q,Sym2.eq_swap (a := c) (b := a),or_left_comm,or_assoc]
  have habK : s(a,b) ∈ K.edgeSet := ⟨hab,by simp [S,F.xa.ne.symm,F.ay],by simp [S,F.xb.ne.symm,F.byy]⟩
  have hacK : s(a,c) ∈ K.edgeSet := (deleteEdges_adj.mp hacH).1
  apply hD.expand_edge_restore_path hacH P hP Q hQ
  · intro z hz hza hzc
    have hzxy : z=x ∨ z=y := by simpa [P,Walk.support,hza,hzc] using hz
    rcases hzxy with rfl | rfl <;> assumption
  · change G.edgeSet=(K.deleteEdges {s(a,b)}).edgeSet \ {s(a,c)} ∪ _ ∪ _
    rw [edgeSet_deleteEdges,hcover0,hQe]
    ext e
    by_cases heB : e=s(a,b)
    · subst e; simp [habK]
    by_cases heC : e=s(a,c)
    · subst e; simp [hacK]
    simp only [Set.mem_union,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,
      heB,heC,false_or,not_false_eq_true,and_true]
  · apply Set.disjoint_left.mpr
    intro e heQ heP
    have hh : List.Disjoint Q.edges P.edges := by
      simp [Q,Q0,P,F.rx.ne,F.ry.ne,F.xy.ne,F.xa.ne,F.xb.ne,F.yc.ne,F.yd.ne,
        F.ar,F.ay,F.ay.symm,F.byy.symm,F.cr,F.cx,F.cx.symm,F.dx.symm,F.ab,F.cd,hac.ne,hbc,ne_comm]
    exact List.disjoint_left.mp hh (Q.mem_edges_toSubgraph.mp heQ) (P.mem_edges_toSubgraph.mp heP)
  · apply Set.disjoint_left.mpr
    intro e heQ heH
    rw [hQe] at heQ
    rcases heQ with (he|he) | he
    · exact heH.2 he
    · have hh := show e ∈ K.edgeSet \ {s(a,b)} from (edgeSet_deleteEdges (s := {s(a,b)}) (G := K)) ▸ heH.1
      exact hh.2 he
    · exact Set.disjoint_left.mp hQ0K he (edgeSet_mono (show H ≤ K from deleteEdges_le _) heH.1)

lemma QuarticData.distinct_pairs_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} {r x y a b c d : Fin n}
    (F : QuarticData G r x y a b c d)
    (hK : SupportConnected (puncture G ({x,y} : Set (Fin n))))
    (hab : G.Adj a b) (hcd : G.Adj c d) (hpairs : s(a,b) ≠ s(c,d)) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  by_cases hac : a=c
  · subst c
    apply F.shared_cross_reduction hsmall hK hcd
    intro hbd
    exact hpairs (by rw [hbd])
  by_cases had : a=d
  · subst d
    apply F.swapY.shared_cross_reduction hsmall hK hcd.symm
    intro hbc
    exact hpairs (by rw [hbc]; exact Sym2.eq_swap)
  by_cases hbc : b=c
  · subst c
    apply F.swapX.shared_cross_reduction hsmall hK hcd
    intro had
    exact hpairs (by rw [had]; exact Sym2.eq_swap)
  by_cases hbd : b=d
  · subst d
    apply F.swapX.swapY.shared_cross_reduction hsmall hK hcd.symm
    intro hac
    exact hpairs (by rw [hac])
  have habK : (puncture G ({x,y} : Set (Fin n))).Adj a b :=
    ⟨hab,by simp [F.xa.ne.symm,F.ay],by simp [F.xb.ne.symm,F.byy]⟩
  have hcdK : (puncture G ({x,y} : Set (Fin n))).Adj c d :=
    ⟨hcd,by simp [F.cx,F.yc.ne.symm],by simp [F.dx,F.yd.ne.symm]⟩
  by_cases hacG : G.Adj a c
  · by_cases hbdG : G.Adj b d
    · exact QuarticData.both_cross_reduction hsmall F hK hab hcd hacG hbdG had hbc
    · exact F.swapX.swapY.fresh_cross_reduction hsmall hK ⟨a,habK.symm⟩ ⟨c,hcdK.symm⟩ hbd hac hbdG
  · exact F.fresh_cross_reduction hsmall hK ⟨b,habK⟩ ⟨d,hcdK⟩ hac hbd hacG

end Erdos583QuarticPairCrossDevelopment
