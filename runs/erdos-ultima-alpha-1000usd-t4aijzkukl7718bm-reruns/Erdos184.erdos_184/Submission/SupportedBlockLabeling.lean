import Submission.AttachmentInterpretation
import Submission.AttachmentModelCompatibility
import Submission.CycleDecompositionEmbeddings
import Submission.QuadrilateralOutsideModels

/-! Combining cycle/outside labels and transporting the certified decomposition
back to an arbitrary ambient graph, with isolated vertices ignored. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.SupportedBlockLabeling
open CountThreeAttachmentData AttachmentModelFacts AttachmentColumns AttachmentModelCompatibility
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 1000000

noncomputable def combined (C : G.Subgraph) (hCS : C.verts ⊆ G.support)
    {l n : ℕ} (ec : Fin l ≃ C.verts) (eo : Fin n ≃ ↥(G.support \ C.verts)) :
    Fin (l+n) ≃ G.support :=
  finSumFinEquiv.symm.trans ((ec.sumCongr eo).trans (Equiv.Set.sumDiffSubset hCS))

lemma combined_left (C : G.Subgraph) (hCS : C.verts ⊆ G.support)
    {l n : ℕ} (ec : Fin l ≃ C.verts) (eo : Fin n ≃ ↥(G.support \ C.verts)) (c : Fin l) :
    (combined C hCS ec eo (Fin.castAdd n c)).val = (ec c).val := by simp [combined]

lemma combined_right (C : G.Subgraph) (hCS : C.verts ⊆ G.support)
    {l n : ℕ} (ec : Fin l ≃ C.verts) (eo : Fin n ≃ ↥(G.support \ C.verts)) (j : Fin n) :
    (combined C hCS ec eo (Fin.natAdd l j)).val = (eo j).val := by simp [combined]

noncomputable def embedding (C : G.Subgraph) (hCS : C.verts ⊆ G.support)
    {l n : ℕ} (ec : Fin l ≃ C.verts) (eo : Fin n ≃ ↥(G.support \ C.verts)) (ht : l+n ≤ 11) :
    G.support ↪ Fin 11 := (combined C hCS ec eo).symm.toEmbedding.trans (Fin.castLEEmb ht)

noncomputable def labeled (C : G.Subgraph) (hCS : C.verts ⊆ G.support)
    {l n : ℕ} (ec : Fin l ≃ C.verts) (eo : Fin n ≃ ↥(G.support \ C.verts)) (ht : l+n ≤ 11) :
    SimpleGraph (Fin 11) := (G.induce G.support).map (embedding C hCS ec eo ht)

lemma labeled_support (C : G.Subgraph) (hCS : C.verts ⊆ G.support)
    {l n : ℕ} (ec : Fin l ≃ C.verts) (eo : Fin n ≃ ↥(G.support \ C.verts)) (ht : l+n ≤ 11)
    (v : Fin 11) (hv : v ∈ (labeled C hCS ec eo ht).support) : v.val < l+n := by
  rw [labeled,support_map] at hv
  obtain ⟨x,_,rfl⟩ := hv
  exact ((combined C hCS ec eo).symm x).isLt

lemma labeled_adj (C : G.Subgraph) (hCS : C.verts ⊆ G.support)
    {l n : ℕ} (ec : Fin l ≃ C.verts) (eo : Fin n ≃ ↥(G.support \ C.verts)) (ht : l+n ≤ 11)
    (a b : Fin (l+n)) :
    (labeled C hCS ec eo ht).Adj (Fin.castLE ht a) (Fin.castLE ht b) ↔
      G.Adj (combined C hCS ec eo a).val (combined C hCS ec eo b).val := by
  have hh := map_adj_apply (G := G.induce G.support) (f := embedding C hCS ec eo ht)
    (a := combined C hCS ec eo a) (b := combined C hCS ec eo b)
  simpa only [embedding,Function.Embedding.trans_apply,Equiv.coe_toEmbedding,
    Fin.castLEEmb_apply,Equiv.symm_apply_apply,induce_adj] using hh

lemma labeled_degree (C : G.Subgraph) (hCS : C.verts ⊆ G.support)
    {l n : ℕ} (ec : Fin l ≃ C.verts) (eo : Fin n ≃ ↥(G.support \ C.verts)) (ht : l+n ≤ 11)
    (a : Fin (l+n)) : (labeled C hCS ec eo ht).degree (Fin.castLE ht a) =
      G.degree (combined C hCS ec eo a).val := by
  have hh := PaddedGraphEncoding.degree_map (G.induce G.support) (embedding C hCS ec eo ht)
    (combined C hCS ec eo a)
  have hI := G.degree_induce_support (combined C hCS ec eo a)
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hI ⊢
  simp only [embedding,Function.Embedding.trans_apply,Equiv.coe_toEmbedding,
    Fin.castLEEmb_apply,Equiv.symm_apply_apply] at hh
  exact hh.trans hI

lemma decomposition_from_labels (i : Fin 12) (C : G.Subgraph)
    (hCS : C.verts ⊆ G.support)
    (ec : Fin (model i).girth ≃ C.verts)
    (eo : Fin (model i).outsideOrder ≃ ↥(G.support \ C.verts))
    (hcbase : ∀ a b, G.Adj (ec a).val (ec b).val ↔
      s(Fin.ofNat 11 a.val,Fin.ofNat 11 b.val) ∈ (model i).base)
    (hobase : ∀ a b, G.Adj (eo a).val (eo b).val ↔
      s(outsideVertex (model i) a.val,outsideVertex (model i) b.val) ∈ (model i).base)
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (htri : (model i).girth = 4 → ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False) :
    ∃ D : Finset G.Subgraph,
      (∀ P ∈ D, P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ 2 := by
  let ht := (model_bounds i).2.2.2.2
  let f := embedding C hCS ec eo ht
  let H := labeled C hCS ec eo ht
  have hsupp : ∀ v ∈ H.support, v.val < (model i).girth + (model i).outsideOrder :=
    labeled_support C hCS ec eo ht
  have hbase : ∀ v w, (v.val < (model i).girth ↔ w.val < (model i).girth) →
      (H.Adj v w ↔ s(v,w) ∈ (model i).base) := by
    intro v w hsame
    by_cases hva : v.val < (model i).girth + (model i).outsideOrder
    · by_cases hwa : w.val < (model i).girth + (model i).outsideOrder
      · by_cases hv : v.val < (model i).girth
        · have hw := hsame.mp hv
          let a : Fin (model i).girth := ⟨v.val,hv⟩
          let b : Fin (model i).girth := ⟨w.val,hw⟩
          have hh := labeled_adj C hCS ec eo ht
            (Fin.castAdd (model i).outsideOrder a) (Fin.castAdd (model i).outsideOrder b)
          rw [combined_left,combined_left] at hh
          change H.Adj v w ↔ G.Adj (ec a).val (ec b).val at hh
          have hc := hcbase a b
          have hcv : Fin.ofNat 11 a.val = v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
          have hcw : Fin.ofNat 11 b.val = w := Fin.ext (Nat.mod_eq_of_lt w.isLt)
          rw [hcv,hcw] at hc
          exact hh.trans hc
        · have hw : ¬w.val < (model i).girth := fun h => hv (hsame.mpr h)
          let a : Fin (model i).outsideOrder := ⟨v.val-(model i).girth,by omega⟩
          let b : Fin (model i).outsideOrder := ⟨w.val-(model i).girth,by omega⟩
          have ha : Fin.castLE ht (Fin.natAdd (model i).girth a) = v := by
            apply Fin.ext
            change (model i).girth + (v.val-(model i).girth) = v.val
            omega
          have hb : Fin.castLE ht (Fin.natAdd (model i).girth b) = w := by
            apply Fin.ext
            change (model i).girth + (w.val-(model i).girth) = w.val
            omega
          have hova : outsideVertex (model i) a.val = v := by
            apply Fin.ext
            rw [outsideVertex_val i a.isLt]
            change (model i).girth + (v.val-(model i).girth) = v.val
            omega
          have hovb : outsideVertex (model i) b.val = w := by
            apply Fin.ext
            rw [outsideVertex_val i b.isLt]
            change (model i).girth + (w.val-(model i).girth) = w.val
            omega
          have hh := labeled_adj C hCS ec eo ht (Fin.natAdd (model i).girth a) (Fin.natAdd (model i).girth b)
          rw [combined_right,combined_right,ha,hb] at hh
          exact hh.trans (by simpa only [hova,hovb] using hobase a b)
      · exact iff_of_false (fun ha => hwa (hsupp w ⟨v,ha.symm⟩))
          (fun he => hwa (base_active i v w he).2)
    · exact iff_of_false (fun ha => hva (hsupp v ⟨w,ha⟩))
        (fun he => hva (base_active i v w he).1)
  have hfourH : ∀ v, v.val < (model i).girth + (model i).outsideOrder → H.degree v = 4 := by
    intro v hv
    let a : Fin ((model i).girth+(model i).outsideOrder) := ⟨v.val,hv⟩
    have hh := labeled_degree C hCS ec eo ht a
    have h4 := hfour (combined C hCS ec eo a).val (combined C hCS ec eo a).property
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh h4 ⊢
    exact hh.trans h4
  have htriH : (model i).girth = 4 → ∀ u v w, H.Adj u v → H.Adj v w → H.Adj w u → False := by
    intro hquad
    exact QuadrilateralOutsideModels.trianglefree_map (G.induce G.support) f
      (fun u v w huv hvw hwu => htri hquad u.val v.val w.val huv hvw hwu)
  obtain ⟨D,hD,hd,hcard⟩ := AttachmentInterpretation.labeled_decomposition i H hbase hsupp hfourH htriH
  obtain ⟨E,hE,he,hEcard⟩ := CycleDecompositionEmbeddings.pull_decomposition (G.induce G.support) f D (by
    intro P hP
    refine ⟨(hD P hP).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hD P hP).2 v) hd
  obtain ⟨F,hF,hf,hFcard⟩ := CycleDecompositionEmbeddings.of_support_decomposition G E (by
    intro P hP
    refine ⟨(hE P hP).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hE P hP).2 v) he
  refine ⟨F,?_,hf,by omega⟩
  intro P hP
  refine ⟨(hF P hP).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hF P hP).2 v

end Erdos184.SupportedBlockLabeling
