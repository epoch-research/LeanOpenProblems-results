import Submission.QuarticPairCross

/-! Suppressing two independent degree-two vertices saves one Gallai path slot. -/
namespace Erdos583DoubleSuppressionPartitionDevelopment
open SimpleGraph Erdos583Work Erdos583SupportSmoothingDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma double_suppression_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {F : SimpleGraph (Fin n)} (hF : SupportConnected F) {x y a b c d : Fin n}
    (hxy : x ≠ y) (hxa : F.Adj x a) (hxb : F.Adj x b) (hyc : F.Adj y c) (hyd : F.Adj y d)
    (hab : a ≠ b) (hcd : c ≠ d) (hay : a ≠ y) (hby : b ≠ y)
    (hNx : ∀ z, F.Adj x z → z=a ∨ z=b) (hNy : ∀ z, F.Adj y z → z=c ∨ z=d)
    (hnab : ¬F.Adj a b) (hncd : ¬F.Adj c d) (hpairs : s(a,b) ≠ s(c,d)) :
    ∃ D : Finset F.Subgraph, GoodDecomposition F D ∧
      D.card+1 ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let X := smooth F x a b
  let H := smooth X y c d
  have hX : SupportConnected X := smooth_support_connected hF hxa hxb hab hNx
  have hxyF : ¬F.Adj x y := fun h ↦ (hNx y h).elim (fun hh ↦ hay hh.symm) (fun hh ↦ hby hh.symm)
  have hyN : X.neighborSet y=F.neighborSet y := smooth_neighborSet hxy.symm hay.symm hby.symm hxyF
  have hycX : X.Adj y c := by change c ∈ X.neighborSet y; rw [hyN]; exact hyc
  have hydX : X.Adj y d := by change d ∈ X.neighborSet y; rw [hyN]; exact hyd
  have hNyX (z : Fin n) (hz : X.Adj y z) : z=c ∨ z=d :=
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
  have hcF : F.support.ncard ≤ n := by simpa only [Nat.card_fin] using F.support.ncard_le_card
  obtain ⟨D,hD,hDc⟩ := LowDegreeAdjacency.smaller_orders_on_support hsmall H hH (by omega)
  obtain ⟨E,hE,hEc⟩ := smooth_lift hycX hydX hcd hNyX hncdX D hD
  obtain ⟨J,hJ,hJc⟩ := smooth_lift hxa hxb hab hNx hnab E hE
  refine ⟨J,hJ,?_⟩
  rw [BridgeGlue.ceil_half] at hDc
  simp only [BridgeGlue.ceil_half,Fintype.card_fin]
  omega

end Erdos583DoubleSuppressionPartitionDevelopment
