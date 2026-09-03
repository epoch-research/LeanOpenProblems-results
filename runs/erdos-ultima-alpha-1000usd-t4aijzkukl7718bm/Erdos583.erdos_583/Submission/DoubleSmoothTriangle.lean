import Submission.SupportSmoothing

/-! A two-vertex reduction when both degree-two shortcut edges are fresh. -/
namespace Erdos583DoubleSmoothTriangleDevelopment
open SimpleGraph Erdos583Work
open Erdos583SupportSmoothingDevelopment Erdos583RestoreTriangleDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma two_smooth_triangle_reduction {V : Type*} [Fintype V] {F G : SimpleGraph V}
    (hFG : F ≤ G) (hF : SupportConnected F) {r x y a b c d : V}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hdis : Disjoint ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V)) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ {s(r,x),s(x,y),s(r,y)})
    (hxa : F.Adj x a) (hxb : F.Adj x b) (hyc : F.Adj y c) (hyd : F.Adj y d)
    (hab : a ≠ b) (hcd : c ≠ d) (hay : a ≠ y) (hby : b ≠ y)
    (hNx : ∀ z, F.Adj x z → z=a ∨ z=b) (hNy : ∀ z, F.Adj y z → z=c ∨ z=d)
    (hnab : ¬F.Adj a b) (hncd : ¬F.Adj c d) (hpairs : s(a,b) ≠ s(c,d)) :
    ∃ H : SimpleGraph V, SupportConnected H ∧ H.support.ncard+2 ≤ G.support.ncard ∧
      ∀ D : Finset H.Subgraph, GoodDecomposition H D →
        ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  let X := smooth F x a b
  let H := smooth X y c d
  have hX : SupportConnected X := smooth_support_connected hF hxa hxb hab hNx
  have hxyF : ¬F.Adj x y := fun h ↦ Set.disjoint_left.mp hdis (Or.inr (Or.inl rfl)) h
  have hyN : X.neighborSet y=F.neighborSet y := smooth_neighborSet hxy.ne.symm hay.symm hby.symm hxyF
  have hycX : X.Adj y c := by change c ∈ X.neighborSet y; rw [hyN]; exact hyc
  have hydX : X.Adj y d := by change d ∈ X.neighborSet y; rw [hyN]; exact hyd
  have hNyX (z : V) (hz : X.Adj y z) : z=c ∨ z=d :=
    hNy z (show z ∈ F.neighborSet y from hyN ▸ hz)
  have hncdX : ¬X.Adj c d := by
    rintro (h|h)
    · exact hncd h.1
    · obtain ⟨he,_⟩ := (edge_adj a b c d).mp h
      rcases he with ⟨hca,hdb⟩ | ⟨hcb,hda⟩
      · exact hpairs (by rw [hca,hdb])
      · exact hpairs (by rw [hcb,hda]; exact Sym2.eq_swap)
  have hH : SupportConnected H := smooth_support_connected hX hycX hydX hcd hNyX
  have hcX : X.support.ncard+1 ≤ F.support.ncard := smooth_support_card hxa hxb
  have hcH : H.support.ncard+1 ≤ X.support.ncard := smooth_support_card hycX hydX
  have hcF : F.support.ncard ≤ G.support.ncard := Set.ncard_mono (support_mono hFG)
  refine ⟨H,hH,by omega,?_⟩
  intro D hD
  obtain ⟨E,hE,hEc⟩ := smooth_lift hycX hydX hcd hNyX hncdX D hD
  obtain ⟨J,hJ,hJc⟩ := smooth_lift hxa hxb hab hNx hnab E hE
  obtain ⟨K,hK,hKc⟩ := restore_triangle_at_support hFG hrx hxy hry hdis hcover
    ⟨x,⟨a,hxa⟩,Or.inr (Or.inl rfl)⟩ J hJ
  exact ⟨K,hK,by omega⟩

lemma two_fresh_shortcuts_triangle_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {F G : SimpleGraph (Fin n)}
    (hFG : F ≤ G) (hF : SupportConnected F) {r x y a b c d : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hdis : Disjoint ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n))) F.edgeSet)
    (hcover : G.edgeSet=F.edgeSet ∪ {s(r,x),s(x,y),s(r,y)})
    (hxa : F.Adj x a) (hxb : F.Adj x b) (hyc : F.Adj y c) (hyd : F.Adj y d)
    (hab : a ≠ b) (hcd : c ≠ d) (hay : a ≠ y) (hby : b ≠ y)
    (hNx : ∀ z, F.Adj x z → z=a ∨ z=b) (hNy : ∀ z, F.Adj y z → z=c ∨ z=d)
    (hnab : ¬F.Adj a b) (hncd : ¬F.Adj c d) (hpairs : s(a,b) ≠ s(c,d)) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  obtain ⟨H,hH,hc,hlift⟩ := two_smooth_triangle_reduction hFG hF hrx hxy hry hdis hcover
    hxa hxb hyc hyd hab hcd hay hby hNx hNy hnab hncd hpairs
  have hcG : G.support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using G.support.ncard_le_card
  exact LowDegreeAdjacency.gallai_of_two_vertex_support_reduction hsmall G H hH (by omega) hlift

end Erdos583DoubleSmoothTriangleDevelopment
