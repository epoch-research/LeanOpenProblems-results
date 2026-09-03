import Submission.LeafPuncture

/-! A fresh quartic shortcut repairs a cubic/quartic triangle at an odd root. -/
namespace Erdos583MixedTriangleFreshDevelopment
open SimpleGraph Erdos583Work Erdos583Work.DegreeThreeReduction
open Erdos583LeafPunctureDevelopment Erdos583SupportSmoothingDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma mixed_triangle_fresh_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {F G : SimpleGraph (Fin n)} (hFG : F ≤ G) (hF : SupportConnected F) {r x y a b c : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hdis : Disjoint ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n))) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ {s(r,x),s(x,y),s(r,y)})
    (hxa : F.Adj x a) (hxb : F.Adj x b) (hyc : F.Adj y c)
    (hab : a ≠ b) (hay : a ≠ y) (hby : b ≠ y) (hcr : c ≠ r) (hcx : c ≠ x)
    (hNx : ∀ v, F.Adj x v → v=a ∨ v=b) (hNy : ∀ v, F.Adj y v → v=c)
    (hnab : ¬F.Adj a b) (hrodd : Odd (Nat.card (F.neighborSet r))) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let K := puncture F ({y} : Set (Fin n))
  let H := smooth K x a b
  have hK : SupportConnected K := puncture_leaf_connected hF hNy
  have hxaK : K.Adj x a := ⟨hxa,hxy.ne,hay⟩
  have hxbK : K.Adj x b := ⟨hxb,hxy.ne,hby⟩
  have hNxK : ∀ v, K.Adj x v → v=a ∨ v=b := fun v hv ↦ hNx v hv.1
  have hH : SupportConnected H := smooth_support_connected hK hxaK hxbK hab hNxK
  have hcardK : K.support.ncard+1 ≤ F.support.ncard := puncture_supported_vertex_card ⟨c,hyc⟩
  have hcardH : H.support.ncard+1 ≤ K.support.ncard := smooth_support_card hxaK hxbK
  have hcardF : F.support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using F.support.ncard_le_card
  apply LowDegreeAdjacency.gallai_of_two_vertex_support_reduction hsmall G H hH (by omega)
  intro D hD
  obtain ⟨E,hE,hEc⟩ := smooth_lift hxaK hxbK hab hNxK (fun h ↦ hnab h.1) D hD
  have hKN : K.neighborSet r=F.neighborSet r := by
    ext v
    constructor
    · exact fun h ↦ h.1
    · intro h
      refine ⟨h,hry.ne,?_⟩
      intro hv
      have hvy : v=y := hv
      exact hcr (hNy r (hvy ▸ h.symm)).symm
  have hroddK : Odd (Nat.card (K.neighborSet r)) := hKN.symm ▸ hrodd
  let P : G.Walk r c := Walk.cons hrx (Walk.cons hxy (Walk.cons (hFG hyc) Walk.nil))
  have hP : P.IsPath := by
    apply Walk.IsPath.mk'
    simp [P,Walk.support,hrx.ne,hry.ne,hcr.symm,hxy.ne,hcx.symm,hyc.ne]
  let J := G.deleteEdges P.toSubgraph.edgeSet
  have hPe : P.toSubgraph.edgeSet=({s(r,x),s(x,y),s(y,c)} : Set (Sym2 (Fin n))) := by
    ext e
    simp [P,or_comm,or_assoc]
  have hFK : F.edgeSet=K.edgeSet ∪ {s(y,c)} := puncture_leaf_edgeSet hyc hNy
  have hGKe : G.edgeSet=K.edgeSet ∪ (P.toSubgraph.edgeSet ∪ {s(y,r)}) := by
    rw [hcover,hFK,hPe]
    ext e
    simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
    tauto
  have hKdis : Disjoint K.edgeSet P.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hp
    rw [hPe] at hp
    rcases hp with rfl | rfl | rfl
    · exact Set.disjoint_left.mp hdis (Or.inl rfl) he.1
    · exact Set.disjoint_left.mp hdis (Or.inr (Or.inl rfl)) he.1
    · exact he.2.1 rfl
  have hyrP : s(y,r) ∉ P.toSubgraph.edgeSet := by
    rw [hPe]
    simp [hry.ne.symm,hxy.ne.symm,hcr.symm,hyc.ne,hrx.ne]
  have hJe : J.edgeSet=insert s(y,r) K.edgeSet := by
    rw [edgeSet_deleteEdges,hGKe]
    ext e
    constructor
    · rintro ⟨he,hn⟩
      rcases he with he | he | he
      · exact Or.inr he
      · exact (hn he).elim
      · exact Or.inl he
    · rintro (he|he)
      · exact ⟨Or.inr (Or.inr he),fun hp ↦ hyrP (he ▸ hp)⟩
      · exact ⟨Or.inl he,fun hp ↦ Set.disjoint_left.mp hKdis he hp⟩
  have hKJ : K ≤ J := by
    intro u v huv
    change s(u,v) ∈ J.edgeSet
    rw [hJe]
    exact Or.inr huv
  have hyrJ : J.Adj y r := by
    change s(y,r) ∈ J.edgeSet
    rw [hJe]
    exact Or.inl rfl
  obtain ⟨E',hE',hE'c⟩ := append_at_odd_to_isolated hKJ hyrJ
    (fun v hv ↦ hv.2.1 rfl) hroddK hJe E hE
  obtain ⟨L,hL,hLc⟩ := restore_path_subgraph ⟨_,_,P,hP,rfl⟩ hE'
  exact ⟨L,hL,by omega⟩

end Erdos583MixedTriangleFreshDevelopment
