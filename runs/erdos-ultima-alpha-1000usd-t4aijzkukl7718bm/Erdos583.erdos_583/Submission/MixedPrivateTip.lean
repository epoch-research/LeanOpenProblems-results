import Submission.PrivateProxy

/-! A cubic triangle tip attached to a quartic vertex's external neighbor is reducible. -/
namespace Erdos583MixedPrivateTipDevelopment
open SimpleGraph Erdos583Work Erdos583PrivateProxyDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma mixed_private_tip_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {r x y a b : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hya : G.Adj y a)
    (har : a ≠ r) (hbr : b ≠ r) (hby : b ≠ y) (hab : a ≠ b)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a ∨ z=b)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=a)
    (hra : (puncture G ({x,y} : Set (Fin n))).Reachable r a)
    (hrb : (puncture G ({x,y} : Set (Fin n))).Reachable r b) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {x,y}
  let H := puncture G S ⊔ edge r b
  have hxH : x ∉ H.support := puncture_fresh_internal (T := S) (Or.inl rfl) hrx.ne.symm hxb.ne
  have hyH : y ∉ H.support := puncture_fresh_internal (T := S) (Or.inr rfl) hry.ne.symm hby.symm
  have hH : SupportConnected H := mixed_boundary_connected hG hNx hNy hxH hyH
    (fun u hu v hv huv ↦ (show H.Adj u v from Or.inl ⟨huv,hu,hv⟩).reachable)
    (hra.mono le_sup_left) (hrb.mono le_sup_left) (hra.mono le_sup_left)
  apply gallai_private_pair_proxy hsmall G H hxy.ne hH hxH hyH
  intro D hD
  let P := Walk.cons hry (Walk.cons hxy.symm (Walk.cons hxb Walk.nil))
  let Q := Walk.cons hrx (Walk.cons hxa (Walk.cons hya.symm Walk.nil))
  have hP : P.IsPath := by
    apply Walk.IsPath.mk'
    simp [P,Walk.support,hry.ne,hrx.ne,hbr.symm,hxy.ne.symm,hby.symm,hxb.ne]
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    simp [Q,Walk.support,hrx.ne,har.symm,hry.ne,hxa.ne,hxy.ne,hya.ne.symm]
  apply puncture_proxy_restore_at_start S hbr.symm P hP Q hQ _ _ _ _ _ _ D hD
  · intro z hz hzr hzb
    simpa [P,Walk.support,hzr,hzb,S,or_comm] using hz
  · rintro z (rfl|rfl) v hv
    · rcases hNx v hv with rfl | rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
    · rcases hNy v hv with rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
  · intro e he
    simp only [Q,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_right _ _⟩
    · exact ⟨x,Or.inl rfl,Sym2.mem_mk_left _ _⟩
    · exact ⟨y,Or.inr rfl,Sym2.mem_mk_right _ _⟩
  · simp [P,Q,hrx.ne,hry.ne,hxy.ne,hxa.ne,hxb.ne,hya.ne,
      har.symm,hbr,hby,hab,ne_comm]
  · simp [P,hrx.ne,hry.ne,hxb.ne,hbr,hby,ne_comm]
  · simp [Q,Walk.support,hbr,hxb.ne.symm,hab.symm,hby]

end Erdos583MixedPrivateTipDevelopment
