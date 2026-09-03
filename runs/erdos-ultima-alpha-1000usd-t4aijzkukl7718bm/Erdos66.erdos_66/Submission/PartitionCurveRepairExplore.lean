import Submission.AbstractSumDifferenceFamilyExplore

/-! Origin repair on several parabolas. A finite partition with small fibers
can be embedded into separate nonzero curves, without using one curve large
enough for the entire repair grid. These are finite statements only. -/
namespace Erdos66PartitionCurveRepair
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66AsymmetricRepair
  Erdos66CrossGraph Erdos66RectangleRepair
open scoped Classical

section Embedding
variable {F α ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype α] [Fintype ι]

/-- Different partition fibers are assigned to different parabolas. -/
theorem partition_curve_embedding (c : α → ι) (w : ι → F)
    (hw : Function.Injective w) (hw0 : ∀ i, w i ≠ 0)
    (hsize : ∀ i, Fintype.card {x : α // c x=i} < Fintype.card F) :
    ∃ f : α → F × F, Function.Injective f ∧
      (∀ x, (f x).1 ≠ 0) ∧ ∀ x, f x ∈ curve (w (c x)) := by
  have hemb : ∀ i, Nonempty ({x : α // c x=i} ↪ {y : F // y ≠ 0}) := by
    intro i
    apply Function.Embedding.nonempty_of_card_le
    have hc : Fintype.card {y : F // y ≠ 0}=Fintype.card F-1 := by
      rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq]
    rw [hc]
    have hh := hsize i
    omega
  let e := fun i ↦ Classical.choice (hemb i)
  let a := fun (i : ι) (x : α) ↦ if h : c x=i then (e i ⟨x,h⟩).val else 1
  let f := fun x : α ↦ (a (c x) x,(a (c x) x)^2/w (c x))
  have ha : ∀ x, a (c x) x ≠ 0 := by
    intro x
    simp only [a,dif_pos rfl]
    exact (e (c x) ⟨x,rfl⟩).property
  have hfcurve : ∀ x, f x ∈ curve (w (c x)) := fun x ↦ (mem_curve _ _).mpr rfl
  refine ⟨f,?_,ha,hfcurve⟩
  intro x y hxy
  have hcolor : c x=c y := by
    by_contra hne
    have hz := curve_intersection (hw0 (c x)) (hw0 (c y))
      (fun he ↦ hne (hw he)) (hfcurve x) (hxy.symm ▸ hfcurve y)
    exact ha x (congrArg Prod.fst hz)
  have heq : a (c x) x=a (c y) y := congrArg Prod.fst hxy
  rw [hcolor] at heq
  simp only [a,dif_pos hcolor,dif_pos rfl] at heq
  exact congrArg Subtype.val ((e (c y)).injective (Subtype.ext heq))

lemma curve_images_no_opposites (c : α → ι) (w : ι → F)
    (hw0 : ∀ i, w i ≠ 0) (hwopp : ∀ i j, w i+w j ≠ 0)
    (f : α → F × F) (hf0 : ∀ x, (f x).1 ≠ 0)
    (hfc : ∀ x, f x ∈ curve (w (c x))) : ∀ x y, f x ≠ -(f y) := by
  intro x y hxy
  have hne : w (c x) ≠ -w (c y) := fun hh ↦ hwopp (c x) (c y) (by rw [hh,neg_add_cancel])
  have hz := curve_intersection (hw0 (c x)) (neg_ne_zero.mpr (hw0 (c y))) hne
    (hfc x) (hxy ▸ neg_mem_curve _ (hfc y))
  exact hf0 x (congrArg Prod.fst hz)

end Embedding

section AbstractRepair
variable {G α : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq α]

noncomputable def pointRepair (f : α → G) (R S : Finset α) : Finset G :=
  R.image f ∪ (S.image f).image Neg.neg

lemma pointRepair_mono (f : α → G) {R R' S S' : Finset α}
    (hR : R ⊆ R') (hS : S ⊆ S') : pointRepair f R S ⊆ pointRepair f R' S' :=
  Finset.union_subset_union (Finset.image_subset_image hR)
    (Finset.image_subset_image (Finset.image_subset_image hS))

lemma image_neg_disjoint (f : α → G) (hopp : ∀ x y, f x ≠ -(f y))
    (R S : Finset α) : Disjoint (R.image f) ((S.image f).image Neg.neg) := by
  apply Finset.disjoint_left.mpr
  intro z hz hnz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hnz
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
  exact hopp x y he.symm

lemma positive_image_origin (f : α → G) (hopp : ∀ x y, f x ≠ -(f y))
    (R S : Finset α) : pairCount (R.image f) (S.image f) 0=0 := by
  rw [pairCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro z hz hn
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hn
  exact hopp x y (by simpa only [zero_sub,neg_neg] using congrArg Neg.neg he.symm)

lemma pointRepair_origin (f : α → G) (hf : Function.Injective f)
    (hopp : ∀ x y, f x ≠ -(f y)) (R S R' S' : Finset α) :
    pairCount (pointRepair f R S) (pointRepair f R' S') 0=
      (R ∩ S').card+(S ∩ R').card := by
  rw [pointRepair,pointRepair,pairCount_union_mixed _ _ _ _ _
    (image_neg_disjoint f hopp R S) (image_neg_disjoint f hopp R' S'),
    positive_image_origin f hopp R R',pairCount_neg_right_zero,
    ← Finset.image_inter _ _ hf,Finset.card_image_of_injective _ hf,
    pairCount_comm ((S.image f).image Neg.neg),pairCount_neg_right_zero,
    ← Finset.image_inter _ _ hf,Finset.card_image_of_injective _ hf,
    pairCount_neg_neg_zero,positive_image_origin f hopp S S',Finset.inter_comm R' S]
  omega

lemma pointRepair_base_origin (A : Finset G) (f : α → G)
    (hpos : ∀ x, f x ∉ A) (hneg : ∀ x, -(f x) ∉ A) (R S : Finset α) :
    pairCount (pointRepair f R S) A 0=0 := by
  rw [pairCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro z hz hnz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact hneg x (by simpa only [zero_sub] using hnz)
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact hpos x (by simpa only [zero_sub,neg_neg] using hnz)

lemma pointRepair_disjoint_base (A : Finset G) (f : α → G)
    (hpos : ∀ x, f x ∉ A) (hneg : ∀ x, -(f x) ∉ A) (R S : Finset α) :
    Disjoint A (pointRepair f R S) := by
  apply Finset.disjoint_left.mpr
  intro z hz hzd
  rcases Finset.mem_union.mp hzd with hzd | hzd
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hzd
    exact hpos x hz
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hzd
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact hneg x hz

end AbstractRepair

section CurveBounds
variable {F α : Type*} [Field F] [Fintype F] [DecidableEq F] [DecidableEq α]

lemma curve_point_not_mem (U : Finset F) (hU : ∀ u∈U, u ≠ 0)
    (w : F) (hw : w ≠ 0) (hwU : w∉U) (z : F × F)
    (hz : z ∈ curve w) (hz0 : z.1 ≠ 0) : z∉parabolaSet U := by
  intro hzu
  obtain ⟨u,hu,he⟩ := (Finset.mem_filter.mp hzu).2
  have hne : w ≠ u := fun hh ↦ hwU (hh.symm ▸ hu)
  have hh := curve_intersection hw (hU u hu) hne hz ((mem_curve _ _).mpr he)
  exact hz0 (congrArg Prod.fst hh)

lemma pointRepair_parabola_subset (f : α → F × F) (R S : Finset α)
    (W : Finset F) (hR : ∀ x∈R, f x ∈ parabolaSet W)
    (hS : ∀ x∈S, f x ∈ parabolaSet W) :
    pointRepair f R S ⊆ parabolaSet (W ∪ W.image Neg.neg) := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact parabolaSet_mono Finset.subset_union_left (hR x hx)
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    have hh : -(f x) ∈ parabolaSet (W.image Neg.neg) := by
      rw [← Erdos66SumDifferenceRepair.parabolaSet_neg]
      exact Finset.mem_image.mpr ⟨f x,hS x hx,rfl⟩
    exact parabolaSet_mono Finset.subset_union_right hh

/-- Off the exceptional origin, only the number of repair curves matters. -/
theorem multiple_curve_error (hF : ringChar F ≠ 2) (U V W W' : Finset F)
    (hU : ∀ u∈U, u ≠ 0) (hV : ∀ v∈V, v ≠ 0)
    (hW : ∀ w∈W, w ≠ 0) (hW' : ∀ w∈W', w ≠ 0)
    (D E : Finset (F × F))
    (hD : D ⊆ parabolaSet (W ∪ W.image Neg.neg))
    (hE : E ⊆ parabolaSet (W' ∪ W'.image Neg.neg))
    (hUD : Disjoint (parabolaSet U) D) (hVE : Disjoint (parabolaSet V) E)
    (z : F × F) (hz : z ≠ 0) :
    pairCount (parabolaSet U) (parabolaSet V) z ≤
      pairCount (parabolaSet U ∪ D) (parabolaSet V ∪ E) z ∧
    pairCount (parabolaSet U ∪ D) (parabolaSet V ∪ E) z ≤
      pairCount (parabolaSet U) (parabolaSet V) z+
        4*U.card*W'.card+4*W.card*V.card+8*W.card*W'.card := by
  have hne (W : Finset F) (hw : ∀ w∈W, w ≠ 0) :
      ∀ w∈W ∪ W.image Neg.neg, w ≠ 0 := by
    intro w hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact hw w hh
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hh
      exact neg_ne_zero.mpr (hw v hv)
  have hcard (W : Finset F) : (W ∪ W.image Neg.neg).card ≤ 2*W.card := by
    have hh := Finset.card_union_le W (W.image Neg.neg)
    rw [Finset.card_image_of_injective _ neg_injective] at hh
    omega
  have h₁ := (pairCount_mono (Finset.Subset.refl _) hE z).trans
    (parabolaSet_pairCount_le hF U (W' ∪ W'.image Neg.neg) hU (hne W' hW') z hz)
  have h₂ := (pairCount_mono hD (Finset.Subset.refl _) z).trans
    (parabolaSet_pairCount_le hF (W ∪ W.image Neg.neg) V (hne W hW) hV z hz)
  have h₃ := (pairCount_mono hD hE z).trans
    (parabolaSet_pairCount_le hF (W ∪ W.image Neg.neg) (W' ∪ W'.image Neg.neg)
      (hne W hW) (hne W' hW') z hz)
  have h₁' : pairCount (parabolaSet U) E z ≤ 4*U.card*W'.card :=
    h₁.trans (by nlinarith [Nat.mul_le_mul_left (2*U.card) (hcard W')])
  have h₂' : pairCount D (parabolaSet V) z ≤ 4*W.card*V.card :=
    h₂.trans (by nlinarith [Nat.mul_le_mul_right (2*V.card) (hcard W)])
  have h₃' : pairCount D E z ≤ 8*W.card*W'.card := by
    apply h₃.trans
    have hh := Nat.mul_le_mul (hcard W) (hcard W')
    nlinarith
  rw [pairCount_union_mixed _ _ _ _ _ hUD hVE]
  omega

end CurveBounds
end Erdos66PartitionCurveRepair
