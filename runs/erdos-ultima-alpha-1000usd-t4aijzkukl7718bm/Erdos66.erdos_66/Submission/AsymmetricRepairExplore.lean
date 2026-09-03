import Submission.ParabolaRepairExplore
import Submission.CrossGraphExplore

/-! A mixed-count origin repair with two independently selected partial
parabolas. This permits simultaneous control of a family of finite sets. -/
namespace Erdos66AsymmetricRepair
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66CrossGraph

section Counts
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma pairCount_neg_right_zero (A B : Finset G) :
    pairCount A (B.image Neg.neg) 0 = (A ∩ B).card := by
  unfold pairCount
  congr 1
  ext x
  simp only [Finset.mem_filter, zero_sub, Finset.mem_image, neg_inj,
    exists_eq_right, Finset.mem_inter]

lemma pairCount_neg_neg_zero (A B : Finset G) :
    pairCount (A.image Neg.neg) (B.image Neg.neg) 0 = pairCount A B 0 := by
  unfold pairCount
  rw [Finset.filter_image, Finset.card_image_of_injective _ neg_injective]
  congr 1
  apply Finset.filter_congr
  intro x hx
  simp only [zero_sub, Finset.mem_image, neg_inj, exists_eq_right]

lemma pairCount_union_mixed (A D B E : Finset G) (z : G)
    (hAD : Disjoint A D) (hBE : Disjoint B E) :
    pairCount (A ∪ D) (B ∪ E) z = pairCount A B z + pairCount A E z +
      pairCount D B z + pairCount D E z := by
  rw [pairCount_union_left _ _ _ _ hAD, pairCount_union_right _ _ _ _ hBE,
    pairCount_union_right _ _ _ _ hBE]
  omega

end Counts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma mem_partialCurve (w : F) (T : Finset F) (z : F × F) :
    z ∈ partialCurve w T ↔ z.1 ∈ T ∧ z.2 = z.1 ^ 2 / w := by
  simp only [partialCurve, Finset.mem_image, Prod.ext_iff]
  constructor
  · rintro ⟨x, hx, he, hy⟩
    exact ⟨he ▸ hx, by simpa only [he] using hy.symm⟩
  · rintro ⟨hx, hy⟩
    exact ⟨z.1, hx, rfl, hy.symm⟩

lemma partialCurve_inter (w : F) (T S : Finset F) :
    partialCurve w T ∩ partialCurve w S = partialCurve w (T ∩ S) := by
  ext z
  simp only [Finset.mem_inter, mem_partialCurve]
  tauto

lemma partialCurve_card (w : F) (T : Finset F) : (partialCurve w T).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ he ↦ congrArg Prod.fst he)

lemma partialCurve_neg_disjoint (hF : ringChar F ≠ 2) (w : F) (hw : w ≠ 0)
    (E F' : Finset F) (hE : (0 : F) ∉ E) :
    Disjoint (partialCurve w E) ((partialCurve w F').image Neg.neg) := by
  apply Finset.disjoint_left.mpr
  intro z hz hzn
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hzn
  have hn : z ∈ curve (-w) := he ▸ neg_mem_curve w (partialCurve_subset w F' hx)
  have hz0 := curve_intersection hw (neg_ne_zero.mpr hw) (parameter_ne_neg hF hw)
    (partialCurve_subset w E hz) hn
  have hzE := ((mem_partialCurve w E z).mp hz).1
  have hx0 : z.1 = 0 := congrArg Prod.fst hz0
  exact hE (hx0 ▸ hzE)

lemma partialCurve_same_origin (hF : ringChar F ≠ 2) (w : F) (hw : w ≠ 0)
    (E F' : Finset F) (hE : (0 : F) ∉ E) :
    pairCount (partialCurve w E) (partialCurve w F') 0 = 0 := by
  rw [pairCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro z hz hnz
  apply Finset.disjoint_left.mp (partialCurve_neg_disjoint hF w hw E F' hE) hz
  exact Finset.mem_image.mpr ⟨-z, by simpa only [zero_sub] using hnz, neg_neg z⟩

noncomputable def asymmetricRepair (w : F) (E F' : Finset F) : Finset (F × F) :=
  partialCurve w E ∪ (partialCurve w F').image Neg.neg

lemma asymmetricRepair_subset (w : F) (E F' : Finset F) :
    asymmetricRepair w E F' ⊆ repairPoints w (E ∪ F') := by
  apply Finset.union_subset_union
  · exact Finset.image_subset_image Finset.subset_union_left
  · exact Finset.image_subset_image (Finset.image_subset_image Finset.subset_union_right)

lemma asymmetricRepair_disjoint (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0)
    (w : F) (hw : w ≠ 0) (hwU : w ∉ U) (hnwU : -w ∉ U)
    (E F' : Finset F) (hE : (0 : F) ∉ E) (hF' : (0 : F) ∉ F') :
    Disjoint (parabolaSet U) (asymmetricRepair w E F') :=
  (repairPoints_disjoint U hU w hw hwU hnwU (E ∪ F') (by simpa using And.intro hE hF')).mono_right
    (asymmetricRepair_subset w E F')

lemma asymmetricRepair_origin (hF : ringChar F ≠ 2) (w : F) (hw : w ≠ 0)
    (E₁ F₁ E₂ F₂ : Finset F) (hE₁ : (0 : F) ∉ E₁) (hF₁ : (0 : F) ∉ F₁)
    (hE₂ : (0 : F) ∉ E₂) :
    pairCount (asymmetricRepair w E₁ F₁) (asymmetricRepair w E₂ F₂) 0 =
      (E₁ ∩ F₂).card + (F₁ ∩ E₂).card := by
  rw [asymmetricRepair, asymmetricRepair,
    pairCount_union_mixed _ _ _ _ _ (partialCurve_neg_disjoint hF w hw E₁ F₁ hE₁)
      (partialCurve_neg_disjoint hF w hw E₂ F₂ hE₂),
    partialCurve_same_origin hF w hw E₁ E₂ hE₁,
    pairCount_neg_right_zero, partialCurve_inter, partialCurve_card,
    pairCount_comm ((partialCurve w F₁).image Neg.neg),
    pairCount_neg_right_zero, partialCurve_inter, partialCurve_card,
    pairCount_neg_neg_zero, partialCurve_same_origin hF w hw F₁ F₂ hF₁,
    Finset.inter_comm E₂ F₁]
  omega

lemma asymmetricRepair_graph_origin (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0)
    (w : F) (hw : w ≠ 0) (hwU : w ∉ U) (hnwU : -w ∉ U)
    (E F' : Finset F) (hE : (0 : F) ∉ E) (hF' : (0 : F) ∉ F') :
    pairCount (asymmetricRepair w E F') (parabolaSet U) 0 = 0 := by
  have hd := repairPoints_disjoint U hU w hw hwU hnwU (E ∪ F')
    (by simpa using And.intro hE hF')
  have hz := disjoint_symmetric_origin (parabolaSet U) (repairPoints w (E ∪ F')) hd
    (repairPoints_symmetric w (E ∪ F'))
  exact Nat.eq_zero_of_le_zero ((pairCount_mono (asymmetricRepair_subset w E F')
    (Finset.Subset.refl _) 0).trans_eq hz)

lemma asymmetricRepair_mixed (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u + v ≠ 0) (hUne : U.Nonempty) (hVne : V.Nonempty)
    (w : F) (hw : w ≠ 0) (hwU : w ∉ U) (hnwU : -w ∉ U) (hwV : w ∉ V) (hnwV : -w ∉ V)
    (E₁ F₁ E₂ F₂ : Finset F)
    (hE₁ : (0 : F) ∉ E₁) (hF₁ : (0 : F) ∉ F₁)
    (hE₂ : (0 : F) ∉ E₂) (hF₂ : (0 : F) ∉ F₂) :
    pairCount (parabolaSet U ∪ asymmetricRepair w E₁ F₁)
        (parabolaSet V ∪ asymmetricRepair w E₂ F₂) 0 =
        1 + (E₁ ∩ F₂).card + (F₁ ∩ E₂).card ∧
      ∀ z : F × F, z ≠ 0 →
        pairCount (parabolaSet U) (parabolaSet V) z ≤
          pairCount (parabolaSet U ∪ asymmetricRepair w E₁ F₁)
            (parabolaSet V ∪ asymmetricRepair w E₂ F₂) z ∧
        pairCount (parabolaSet U ∪ asymmetricRepair w E₁ F₁)
            (parabolaSet V ∪ asymmetricRepair w E₂ F₂) z ≤
          pairCount (parabolaSet U) (parabolaSet V) z + 4 * U.card + 4 * V.card + 8 := by
  have hdU := asymmetricRepair_disjoint U hU w hw hwU hnwU E₁ F₁ hE₁ hF₁
  have hdV := asymmetricRepair_disjoint V hV w hw hwV hnwV E₂ F₂ hE₂ hF₂
  have hbase : ∀ v ∈ ({w, -w} : Finset F), v ≠ 0 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hw
    · exact neg_ne_zero.mpr hw
  have hcard : ({w, -w} : Finset F).card = 2 := by simp [parameter_ne_neg hF hw]
  have hs₁ : asymmetricRepair w E₁ F₁ ⊆ parabolaSet {w, -w} :=
    (asymmetricRepair_subset w E₁ F₁).trans (repairPoints_subset w (E₁ ∪ F₁))
  have hs₂ : asymmetricRepair w E₂ F₂ ⊆ parabolaSet {w, -w} :=
    (asymmetricRepair_subset w E₂ F₂).trans (repairPoints_subset w (E₂ ∪ F₂))
  constructor
  · rw [pairCount_union_mixed _ _ _ _ _ hdU hdV,
      cross_graph_origin hF U V hU hV hUV hUne hVne,
      pairCount_comm (parabolaSet U) (asymmetricRepair w E₂ F₂),
      asymmetricRepair_graph_origin U hU w hw hwU hnwU E₂ F₂ hE₂ hF₂,
      asymmetricRepair_graph_origin V hV w hw hwV hnwV E₁ F₁ hE₁ hF₁,
      asymmetricRepair_origin hF w hw E₁ F₁ E₂ F₂ hE₁ hF₁ hE₂]
    omega
  · intro z hz
    have h₁ := (pairCount_mono (Finset.Subset.refl _) hs₂ z).trans
      (parabolaSet_pairCount_le hF U {w, -w} hU hbase z hz)
    have h₂ := (pairCount_mono hs₁ (Finset.Subset.refl _) z).trans
      (parabolaSet_pairCount_le hF {w, -w} V hbase hV z hz)
    have h₃ := (pairCount_mono hs₁ hs₂ z).trans
      (parabolaSet_pairCount_le hF {w, -w} {w, -w} hbase hbase z hz)
    rw [hcard] at h₁ h₂ h₃
    rw [pairCount_union_mixed _ _ _ _ _ hdU hdV]
    constructor <;> omega

end Erdos66AsymmetricRepair
