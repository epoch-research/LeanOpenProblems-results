import Submission.MixedPrivateTip

/-! A fresh cross-edge allows a two-vertex reduction of a cubic/quartic triangle. -/
namespace Erdos583MixedPrivateFreshDevelopment
open SimpleGraph Erdos583Work Erdos583PrivateProxyDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma mixed_private_fresh_cross_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {r x y a b c : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hyc : G.Adj y c)
    (har : a ≠ r) (hbr : b ≠ r) (hay : a ≠ y) (hby : b ≠ y)
    (hab : a ≠ b) (hcr : c ≠ r) (hcx : c ≠ x) (hac : a ≠ c)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a ∨ z=b)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=c)
    (hra : (puncture G ({x,y} : Set (Fin n))).Reachable r a)
    (hrb : (puncture G ({x,y} : Set (Fin n))).Reachable r b)
    (hnac : ¬G.Adj a c) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {x,y}
  let H := puncture G S ⊔ edge a c
  have hxH : x ∉ H.support := puncture_fresh_internal (T := S) (Or.inl rfl) hxa.ne hcx.symm
  have hyH : y ∉ H.support := puncture_fresh_internal (T := S) (Or.inr rfl) hay.symm hyc.ne
  have hacH : H.Adj a c := Or.inr ((edge_adj a c a c).mpr ⟨Or.inl ⟨rfl,rfl⟩,hac⟩)
  have hH : SupportConnected H := mixed_boundary_connected hG hNx hNy hxH hyH
    (fun u hu v hv huv ↦ (show H.Adj u v from Or.inl ⟨huv,hu,hv⟩).reachable)
    (hra.mono le_sup_left) (hrb.mono le_sup_left) ((hra.mono le_sup_left).trans hacH.reachable)
  apply gallai_private_pair_proxy hsmall G H hxy.ne hH hxH hyH
  intro D hD
  let P := Walk.cons hxa.symm (Walk.cons hxy (Walk.cons hyc Walk.nil))
  let Q := Walk.cons hxb.symm (Walk.cons hrx.symm (Walk.cons hry Walk.nil))
  have hP : P.IsPath := by
    apply Walk.IsPath.mk'
    simp [P,Walk.support,hxa.ne.symm,hay,hac,hxy.ne,hcx.symm,hyc.ne]
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    simp [Q,Walk.support,hxb.ne.symm,hbr,hby,hrx.ne.symm,hxy.ne,hry.ne]
  apply hD.puncture_expand_restore S hac (fun he ↦ hnac he.1) P hP Q hQ
  · intro z hz hza hzc
    simpa [P,Walk.support,hza,hzc,S] using hz
  · rintro z (rfl|rfl) v hv
    · rcases hNx v hv with rfl | rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
    · rcases hNy v hv with rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
  · intro e he
    simp only [Q,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_right _ _⟩
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_left _ _⟩
    · exact ⟨y,Or.inr rfl,Sym2.mem_mk_right _ _⟩
  · simp [P,Q,hrx.ne,hry.ne,hxy.ne,hxb.ne,hyc.ne,
      har,hay,hby.symm,hab,hcr.symm,hcx,ne_comm]

end Erdos583MixedPrivateFreshDevelopment
