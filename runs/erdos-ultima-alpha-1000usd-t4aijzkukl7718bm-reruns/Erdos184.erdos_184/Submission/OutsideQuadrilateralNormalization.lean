import Submission.QuadrilateralOutsideModels

/-! Normalization of an actual quadrilateral-outside graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.OutsideQuadrilateralNormalization
open HighGirthCritical EvenCycleCore SmallGraphEncoding
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma quadrilateral_outside_normalized {G : SimpleGraph V}
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hind : C.IsInduced) (hquad : C.verts.ncard = 4)
    (hout : NoTwoCycles (avoid G C.verts)) :
    ∃ (n code : ℕ) (hn : n ≤ 7) (e : Fin n ≃ ↥(G.support \ C.verts)),
      code ∈ QuadrilateralOutsideData.patterns n ∧
      graph 7 2 code = (G.induce (G.support \ C.verts)).map
        (e.symm.toEmbedding.trans (Fin.castLEEmb hn)) := by
  obtain ⟨hlo,hhi,hdeg,he,_⟩ :=
    OutsideQuadrilateralData.quadrilateral_outside_data hfour htri C hc hind hquad hout
  have hcard : Fintype.card ↥(G.support \ C.verts) = (G.support \ C.verts).ncard := by
    simp only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨code,e,hgood,henc⟩ := QuadrilateralOutsideModels.exists_normalized
    (G.induce (G.support \ C.verts)) hcard hlo hhi
    (fun v => (hdeg v).1) (fun v => (hdeg v).2) he
    (fun u v w huv hvw hwu => htri u.val v.val w.val huv hvw hwu)
  exact ⟨_,code,hhi,e,hgood,henc⟩

end Erdos184.OutsideQuadrilateralNormalization
