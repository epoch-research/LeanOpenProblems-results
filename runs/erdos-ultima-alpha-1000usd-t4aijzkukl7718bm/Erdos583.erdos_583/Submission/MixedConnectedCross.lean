import Submission.PunctureConnectivity

/-! The both-cross-edge repair needs connected punctured support, not a root-to-tip edge. -/
namespace Erdos583MixedConnectedCrossDevelopment
open SimpleGraph Erdos583Work Erdos583PrivateProxyDevelopment
open Erdos583PunctureConnectivityDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma mixed_connected_both_cross_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} {r x y a b c : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hyc : G.Adj y c)
    (har : a ≠ r) (hbr : b ≠ r) (hay : a ≠ y) (hby : b ≠ y)
    (habG : G.Adj a b) (hcr : c ≠ r) (hcx : c ≠ x) (hca : c ≠ a) (hcb : c ≠ b)
    (hac : G.Adj a c) (hbc : G.Adj b c)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a ∨ z=b)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=c)
    (hKconn : SupportConnected (puncture G ({x,y} : Set (Fin n)))) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {x,y}
  let K := puncture G S
  let H := K.deleteEdges {s(a,c)}
  have hxH : x ∉ H.support := by
    rintro ⟨v,hv⟩
    exact (deleteEdges_adj.mp hv).1.2.1 (Or.inl rfl)
  have hyH : y ∉ H.support := by
    rintro ⟨v,hv⟩
    exact (deleteEdges_adj.mp hv).1.2.1 (Or.inr rfl)
  have habH : H.Adj a b := deleteEdges_adj.mpr
    ⟨⟨habG,by simp [S,hxa.ne.symm,hay],by simp [S,hxb.ne.symm,hby]⟩,
      by simp [hcb.symm,habG.ne.symm]⟩
  have hbcH : H.Adj b c := deleteEdges_adj.mpr
    ⟨⟨hbc,by simp [S,hxb.ne.symm,hby],by simp [S,hcx,hyc.ne.symm]⟩,
      by simp [habG.ne.symm,hca]⟩
  have hH : SupportConnected H := supported_delete_edge_connected hKconn
    (habH.reachable.trans hbcH.reachable)
  apply gallai_private_pair_proxy hsmall G H hxy.ne hH hxH hyH
  intro D hD
  let P := Walk.cons hxb.symm (Walk.cons hxy (Walk.cons hyc Walk.nil))
  let Q0 := Walk.cons hxa.symm (Walk.cons hrx.symm (Walk.cons hry Walk.nil))
  let Q := Walk.cons hbc (Walk.cons hac.symm Q0)
  have hP : P.IsPath := by
    apply Walk.IsPath.mk'
    simp [P,Walk.support,hxb.ne.symm,hby,hcb.symm,hxy.ne,hcx.symm,hyc.ne]
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    simp [Q,Q0,Walk.support,hbc.ne,habG.ne.symm,hxb.ne.symm,hbr,hby,hca,hcx,hcr,hyc.ne.symm,
      hxa.ne.symm,har,hay,hrx.ne.symm,hxy.ne,hry.ne]
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
  have hQe : Q.toSubgraph.edgeSet={s(b,c),s(a,c)} ∪ Q0.toSubgraph.edgeSet := by
    ext e
    simp [Q,Sym2.eq_swap (a := c) (b := a),or_left_comm,or_assoc]
  have hacK : s(a,c) ∈ K.edgeSet := ⟨hac,by simp [S,hxa.ne.symm,hay],by simp [S,hcx,hyc.ne.symm]⟩
  have hbcK : s(b,c) ∈ K.edgeSet := (deleteEdges_adj.mp hbcH).1
  apply hD.expand_edge_restore_path hbcH P hP Q hQ
  · intro z hz hzt hzc
    have hzxy : z=x ∨ z=y := by simpa [P,Walk.support,hzt,hzc] using hz
    rcases hzxy with rfl | rfl <;> assumption
  · change G.edgeSet=(K.deleteEdges {s(a,c)}).edgeSet \ {s(b,c)} ∪ _ ∪ _
    rw [edgeSet_deleteEdges,hcover0,hQe]
    ext e
    by_cases heS : e=s(a,c)
    · subst e; simp [hacK]
    by_cases heT : e=s(b,c)
    · subst e; simp [hbcK]
    simp only [Set.mem_union,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,
      heS,heT,false_or,not_false_eq_true,and_true]
  · apply Set.disjoint_left.mpr
    intro e heQ heP
    have hh : List.Disjoint Q.edges P.edges := by
      simp [Q,Q0,P,hrx.ne,hry.ne,hxy.ne,habG.ne,hbr,hay.symm,hxb.ne.symm,hby,hby.symm,
        hxa.ne,hxb.ne,hyc.ne,hcr,hcx,hcx.symm,hca,hcb,ne_comm]
    exact List.disjoint_left.mp hh (Q.mem_edges_toSubgraph.mp heQ) (P.mem_edges_toSubgraph.mp heP)
  · apply Set.disjoint_left.mpr
    intro e heQ heH
    rw [hQe] at heQ
    rcases heQ with (he|he) | he
    · exact heH.2 he
    · have hh := show e ∈ K.edgeSet \ {s(a,c)} from (edgeSet_deleteEdges (s := {s(a,c)}) (G := K)) ▸ heH.1
      exact hh.2 he
    · exact Set.disjoint_left.mp hQ0K he (edgeSet_mono (show H ≤ K from deleteEdges_le _) heH.1)

end Erdos583MixedConnectedCrossDevelopment
