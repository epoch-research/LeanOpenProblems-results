import Submission.AttachmentRows

/-! Every labeled four-regular graph matching an attachment base model has
an actual decomposition into at most two cycles. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.AttachmentInterpretation
open CountThreeAttachmentData AttachmentModelFacts AttachmentColumns AttachmentRows
set_option maxHeartbeats 1000000

lemma cross_mem_fullEdges (i : Fin 12) (G : SimpleGraph (Fin 11))
    (hsupp : ∀ v ∈ G.support, v.val < (model i).girth + (model i).outsideOrder)
    {v w : Fin 11} (hv : v.val < (model i).girth) (hw : ¬w.val < (model i).girth)
    (ha : G.Adj v w) : s(v,w) ∈ fullEdges (model i) (config G (model i)) := by
  have hb := model_bounds i
  have hws := hsupp w ⟨v,ha.symm⟩
  let c : Fin 4 := ⟨v.val,by omega⟩
  let j := w.val - (model i).girth
  have hj : j < (model i).outsideOrder := by dsimp only [j]; omega
  have hcv : cycleVertex c = v := Fin.ext (cycleVertex_val c)
  have hjw : outsideVertex (model i) j = w := by
    apply Fin.ext
    rw [outsideVertex_val i hj]
    dsimp only [j]
    omega
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨j,Finset.mem_range.mpr hj,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨c,?_,?_⟩
  · rw [config_getD G (model i) hj]
    apply (mem_column G (model i) j c).mpr
    exact ⟨hv,by rwa [hcv,hjw]⟩
  · change s(cycleVertex c,outsideVertex (model i) j) = s(v,w)
    rw [hcv,hjw]

lemma fullEdges_eq (i : Fin 12) (G : SimpleGraph (Fin 11))
    (hbase : ∀ v w, (v.val < (model i).girth ↔ w.val < (model i).girth) →
      (G.Adj v w ↔ s(v,w) ∈ (model i).base))
    (hsupp : ∀ v ∈ G.support, v.val < (model i).girth + (model i).outsideOrder) :
    fullEdges (model i) (config G (model i)) = G.edgeFinset := by
  apply Finset.Subset.antisymm
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · induction e using Sym2.ind with
      | h v w => exact G.mem_edgeFinset.mpr ((hbase _ _ (base_same_side i _ _ he)).mpr he)
    · obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp he
      rw [config_getD G (model i) (Finset.mem_range.mp hj)] at hc
      exact G.mem_edgeFinset.mpr ((mem_column G (model i) j c).mp hc).2
  · intro e he
    induction e using Sym2.ind with
    | h v w =>
      have ha := G.mem_edgeFinset.mp he
      by_cases hv : v.val < (model i).girth
      · by_cases hw : w.val < (model i).girth
        · exact Finset.mem_union_left _ ((hbase _ _ (by simp only [hv,hw])).mp ha)
        · exact cross_mem_fullEdges i G hsupp hv hw ha
      · by_cases hw : w.val < (model i).girth
        · simpa only [Sym2.eq_swap] using cross_mem_fullEdges i G hsupp hw hv ha.symm
        · exact Finset.mem_union_left _ ((hbase _ _ (by simp only [hv,hw])).mp ha)

lemma labeled_decomposition (i : Fin 12) (G : SimpleGraph (Fin 11))
    (hbase : ∀ v w, (v.val < (model i).girth ↔ w.val < (model i).girth) →
      (G.Adj v w ↔ s(v,w) ∈ (model i).base))
    (hsupp : ∀ v ∈ G.support, v.val < (model i).girth + (model i).outsideOrder)
    (hfour : ∀ v, v.val < (model i).girth + (model i).outsideOrder → G.degree v = 4)
    (htri : (model i).girth = 4 → ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ 2 := by
  have hc := config_choices i G hbase hfour htri
  have hv := config_valid i G hbase hsupp hfour htri
  have hh := model_completion i (config G (model i)) hc hv
  have hgraph : fromEdgeSet (fullEdges (model i) (config G (model i)) : Set (Sym2 (Fin 11))) = G := by
    rw [fullEdges_eq i G hbase hsupp]
    simp only [coe_edgeFinset,fromEdgeSet_edgeSet]
  dsimp only at hh
  simp only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
  rw [hgraph] at hh
  exact hh

end Erdos184.AttachmentInterpretation
