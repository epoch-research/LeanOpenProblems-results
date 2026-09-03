import Submission.MixedPrivateFresh

/-! When both cross-edges exist, delete one, expand the other, and restore one five-edge path. -/
namespace Erdos583MixedPrivateBothCrossDevelopment
open SimpleGraph Erdos583Work Erdos583PrivateProxyDevelopment
open Erdos583TriangleTailRootTemplatesDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma mixed_private_both_cross_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {r x y s t c : Fin n}
    (F : Frame G r x y s t) (hxs : G.Adj x s) (hxt : G.Adj x t) (hyc : G.Adj y c)
    (hcr : c ≠ r) (hcx : c ≠ x) (hcs : c ≠ s) (hct : c ≠ t)
    (hsc : G.Adj s c) (htc : G.Adj t c)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=s ∨ z=t)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=c) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {x,y}
  let K := puncture G S
  let H := K.deleteEdges {s(s,c)}
  have hxH : x ∉ H.support := by
    rintro ⟨v,hv⟩
    exact (deleteEdges_adj.mp hv).1.2.1 (Or.inl rfl)
  have hyH : y ∉ H.support := by
    rintro ⟨v,hv⟩
    exact (deleteEdges_adj.mp hv).1.2.1 (Or.inr rfl)
  have hrsH : H.Adj r s := deleteEdges_adj.mpr
    ⟨⟨F.rs,by simp [S,F.rx.ne,F.ry.ne],by simp [S,F.sx,F.sy]⟩,by simp [hcr.symm,F.rs.ne]⟩
  have hstH : H.Adj s t := deleteEdges_adj.mpr
    ⟨⟨F.st,by simp [S,F.sx,F.sy],by simp [S,F.tx,F.ty]⟩,by simp [hct.symm,F.st.ne.symm]⟩
  have htcH : H.Adj t c := deleteEdges_adj.mpr
    ⟨⟨htc,by simp [S,F.tx,F.ty],by simp [S,hcx,hyc.ne.symm]⟩,by simp [F.st.ne.symm,hcs]⟩
  have hscH : H.Reachable s c := hstH.reachable.trans htcH.reachable
  have hrest (u : Fin n) (hu : u ∉ ({x,y} : Set (Fin n))) (v : Fin n)
      (hv : v ∉ ({x,y} : Set (Fin n))) (huv : G.Adj u v) : H.Reachable u v := by
    by_cases he : s(u,v)=s(s,c)
    · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hscH
      · exact hscH.symm
    · exact (show H.Adj u v from deleteEdges_adj.mpr ⟨⟨huv,hu,hv⟩,he⟩).reachable
  have hH : SupportConnected H := mixed_boundary_connected hG hNx hNy hxH hyH hrest
    hrsH.reachable (hrsH.reachable.trans hstH.reachable) (hrsH.reachable.trans hscH)
  apply gallai_private_pair_proxy hsmall G H F.xy.ne hH hxH hyH
  intro D hD
  let P := Walk.cons hxt.symm (Walk.cons F.xy (Walk.cons hyc Walk.nil))
  let Q0 := Walk.cons hxs.symm (Walk.cons F.rx.symm (Walk.cons F.ry Walk.nil))
  let Q := Walk.cons htc (Walk.cons hsc.symm Q0)
  have hP : P.IsPath := by
    apply Walk.IsPath.mk'
    simp [P,Walk.support,F.tx,F.ty,hct.symm,F.xy.ne,hcx.symm,hyc.ne]
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    simp [Q,Q0,Walk.support,htc.ne,F.st.ne.symm,F.tx,F.tr,F.ty,hcs,hcx,hcr,hyc.ne.symm,
      F.sx,F.rs.ne.symm,F.sy,F.rx.ne.symm,F.xy.ne,F.ry.ne]
  have htouch : ∀ e ∈ Q0.edges, ∃ z ∈ S, z ∈ e := by
    intro e he
    simp only [Q0,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_right _ _⟩
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_left _ _⟩
    · exact ⟨y,Or.inr rfl,Sym2.mem_mk_right _ _⟩
  have hQ0K := puncture_disjoint_walk S Q0 htouch
  have hcover0 : G.edgeSet=K.edgeSet ∪ P.toSubgraph.edgeSet ∪ Q0.toSubgraph.edgeSet :=
    puncture_two_walks_cover S P Q0 (by
      rintro z (rfl|rfl) v hv
      · rcases hNx v hv with rfl | rfl | rfl | rfl <;> simp [P,Q0,Sym2.eq_swap]
      · rcases hNy v hv with rfl | rfl | rfl <;> simp [P,Q0,Sym2.eq_swap])
  have hQe : Q.toSubgraph.edgeSet={s(t,c),s(s,c)} ∪ Q0.toSubgraph.edgeSet := by
    ext e
    simp [Q,Sym2.eq_swap (a := c) (b := s),or_left_comm,or_assoc]
  have hscK : s(s,c) ∈ K.edgeSet := ⟨hsc,by simp [S,F.sx,F.sy],by simp [S,hcx,hyc.ne.symm]⟩
  have htcK : s(t,c) ∈ K.edgeSet := (deleteEdges_adj.mp htcH).1
  apply hD.expand_edge_restore_path htcH P hP Q hQ
  · intro z hz hzt hzc
    have hzxy : z=x ∨ z=y := by simpa [P,Walk.support,hzt,hzc] using hz
    rcases hzxy with rfl | rfl <;> assumption
  · change G.edgeSet=(K.deleteEdges {s(s,c)}).edgeSet \ {s(t,c)} ∪ _ ∪ _
    rw [edgeSet_deleteEdges,hcover0,hQe]
    ext e
    by_cases heS : e=s(s,c)
    · subst e; simp [hscK]
    by_cases heT : e=s(t,c)
    · subst e; simp [htcK]
    simp only [Set.mem_union,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,
      heS,heT,false_or,not_false_eq_true,and_true]
  · apply Set.disjoint_left.mpr
    intro e heQ heP
    have hh : List.Disjoint Q.edges P.edges := by
      simp [Q,Q0,P,F.rx.ne,F.ry.ne,F.xy.ne,F.st.ne,F.tr,F.sy.symm,F.tx,F.ty,F.ty.symm,
        hxs.ne,hxt.ne,hyc.ne,hcr,hcx,hcx.symm,hcs,hct,ne_comm]
    exact List.disjoint_left.mp hh (Q.mem_edges_toSubgraph.mp heQ) (P.mem_edges_toSubgraph.mp heP)
  · apply Set.disjoint_left.mpr
    intro e heQ heH
    rw [hQe] at heQ
    rcases heQ with (he|he) | he
    · exact heH.2 he
    · have hh := show e ∈ K.edgeSet \ {s(s,c)} from (edgeSet_deleteEdges (s := {s(s,c)}) (G := K)) ▸ heH.1
      exact hh.2 he
    · exact Set.disjoint_left.mp hQ0K he (edgeSet_mono (show H ≤ K from deleteEdges_le _) heH.1)

end Erdos583MixedPrivateBothCrossDevelopment
