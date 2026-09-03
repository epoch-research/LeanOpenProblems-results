import Submission.CubicTwinsFresh

/-! A present common-neighbor shortcut repairs a cubic true-twin pair. -/
namespace Erdos583CubicTwinsExistingDevelopment
open SimpleGraph Erdos583Work Erdos583PrivateProxyDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma cubic_twins_existing_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} {r x y a : Fin n}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hya : G.Adj y a) (hra : G.Adj r a)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=a)
    (hK : SupportConnected (puncture G ({x,y} : Set (Fin n)))) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {x,y}
  let K := puncture G S
  apply gallai_private_pair_proxy hsmall G K hxy.ne hK
  · rintro ⟨z,hz⟩; exact hz.2.1 (Or.inl rfl)
  · rintro ⟨z,hz⟩; exact hz.2.1 (Or.inr rfl)
  intro D hD
  have hraK : K.Adj r a := ⟨hra,by simp [S,hrx.ne,hry.ne],by simp [S,hxa.ne.symm,hya.ne.symm]⟩
  let P := Walk.cons hrx (Walk.cons hxy (Walk.cons hya Walk.nil))
  let Q := Walk.cons hxa (Walk.cons hra.symm (Walk.cons hry Walk.nil))
  have hP : P.IsPath := by
    apply Walk.IsPath.mk'
    simp [P,Walk.support,hrx.ne,hry.ne,hra.ne,hxy.ne,hxa.ne,hya.ne]
  have hQ : Q.IsPath := by
    apply Walk.IsPath.mk'
    simp [Q,Walk.support,hxa.ne,hrx.ne.symm,hxy.ne,hra.ne.symm,hya.ne.symm,hry.ne]
  have hcover : G.edgeSet=(K.edgeSet ∪ P.toSubgraph.edgeSet) ∪ Q.toSubgraph.edgeSet := by
    apply puncture_two_walks_cover S P Q
    rintro t (rfl|rfl) z hz
    · rcases hNx z hz with rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
    · rcases hNy z hz with rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
  apply hD.expand_edge_restore_path hraK P hP Q hQ
  · intro z hz hzr hza
    have hh : z ∈ S := by simpa [P,Walk.support,hzr,hza,S] using hz
    rintro ⟨w,hw⟩
    exact hw.2.1 hh
  · rw [hcover]
    have hmem : s(r,a) ∈ Q.toSubgraph.edgeSet := by simp [Q,Sym2.eq_swap]
    ext e
    simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]
    constructor
    · rintro ((hh|hh)|hh)
      · by_cases he : e=s(r,a)
        · exact Or.inr (he ▸ hmem)
        · exact Or.inl (Or.inl ⟨hh,he⟩)
      · exact Or.inl (Or.inr hh)
      · exact Or.inr hh
    · tauto
  · simp [Set.disjoint_left,P,Q,hrx.ne,hrx.ne.symm,hry.ne,hry.ne.symm,hxy.ne,hxy.ne.symm,
      hxa.ne,hxa.ne.symm,hya.ne,hya.ne.symm,hra.ne,hra.ne.symm]
  · apply Set.disjoint_left.mpr
    intro e he hh
    simp only [Q,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · exact hh.1.2.1 (Or.inl rfl)
    · exact hh.2 Sym2.eq_swap
    · exact hh.1.2.2 (Or.inr rfl)

end Erdos583CubicTwinsExistingDevelopment
