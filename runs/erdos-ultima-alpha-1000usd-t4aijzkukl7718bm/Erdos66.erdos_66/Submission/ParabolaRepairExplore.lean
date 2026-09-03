import Submission.CosetExplore

/-! A prime-field-friendly origin repair: add a partial parabola together with
its negative. The repair changes each nonzero-target count by only `O(|U|)`.
This is a finite construction, not an infinite witness for Erdős 66. -/
namespace Erdos66ParabolaRepair
open Erdos66OriginRepair Erdos66FiniteField Erdos66Coset

section GeneralCounting
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma pairCount_mono {A B C D : Finset G} (hAC : A ⊆ C) (hBD : B ⊆ D) (z : G) :
    pairCount A B z ≤ pairCount C D z := by
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨hAC (Finset.mem_filter.mp hx).1,
    hBD (Finset.mem_filter.mp hx).2⟩

lemma pairCount_biUnion_left_le {ι : Type*} (S : Finset ι) (A : ι → Finset G)
    (B : Finset G) (z : G) :
    pairCount (S.biUnion A) B z ≤ ∑ i ∈ S, pairCount (A i) B z := by
  classical
  unfold pairCount
  rw [Finset.filter_biUnion]
  exact Finset.card_biUnion_le

lemma pairCount_biUnion_right_le {ι : Type*} (S : Finset ι) (A : ι → Finset G)
    (B : Finset G) (z : G) :
    pairCount B (S.biUnion A) z ≤ ∑ i ∈ S, pairCount B (A i) z := by
  rw [pairCount_comm]
  simpa only [pairCount_comm (A _) B] using pairCount_biUnion_left_le S A B z

lemma symmetric_origin (D : Finset G) (hD : ∀ x ∈ D, -x ∈ D) :
    pairCount D D 0 = D.card := by
  unfold pairCount
  congr 1
  apply Finset.filter_eq_self.mpr
  intro x hx
  simpa only [zero_sub] using hD x hx

end GeneralCounting

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def curve (u : F) : Finset (F × F) :=
  Finset.univ.image (fun x ↦ (x, x ^ 2 / u))

lemma mem_curve (u : F) (z : F × F) : z ∈ curve u ↔ z.2 = z.1 ^ 2 / u := by
  simp only [curve, Finset.mem_image, Finset.mem_univ, true_and, Prod.ext_iff]
  constructor
  · rintro ⟨x, hx, hy⟩
    simpa only [hx] using hy.symm
  · intro h
    exact ⟨z.1, rfl, h.symm⟩

lemma parabolaSet_eq_biUnion (U : Finset F) : parabolaSet U = U.biUnion curve := by
  ext z
  simp [parabolaSet, mem_curve]

lemma curve_pairCount (u v t s : F) :
    pairCount (curve u) (curve v) (t, s) =
      Fintype.card {x : F // x ^ 2 / u + (t - x) ^ 2 / v = s} := by
  unfold pairCount
  rw [show curve u = Finset.univ.image (fun x : F ↦ (x, x ^ 2 / u)) from rfl,
    Finset.filter_image, Finset.card_image_of_injective _
      (fun _ _ h ↦ congrArg Prod.fst h)]
  rw [Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro x hx
  rw [mem_curve]
  dsimp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd]
  constructor <;> intro h <;> linear_combination -h

lemma curve_pairCount_le_two (hF : ringChar F ≠ 2) (u v : F) (hu : u ≠ 0) (hv : v ≠ 0)
    (z : F × F) (hz : z ≠ 0) : pairCount (curve u) (curve v) z ≤ 2 := by
  obtain ⟨t, s⟩ := z
  rw [curve_pairCount]
  have hh := parabola_difference_count_le_two hF u (-v) t s hu (neg_ne_zero.mpr hv) hz
  simp only [div_neg, sub_neg_eq_add] at hh
  exact_mod_cast hh

lemma parabolaSet_pairCount_le (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (z : F × F) (hz : z ≠ 0) :
    pairCount (parabolaSet U) (parabolaSet V) z ≤ 2 * U.card * V.card := by
  rw [parabolaSet_eq_biUnion U, parabolaSet_eq_biUnion V]
  calc
    _ ≤ ∑ u ∈ U, pairCount (curve u) (V.biUnion curve) z :=
      pairCount_biUnion_left_le U curve _ z
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, pairCount (curve u) (curve v) z :=
      Finset.sum_le_sum (fun u _ ↦ pairCount_biUnion_right_le V curve (curve u) z)
    _ ≤ ∑ _u ∈ U, ∑ _v ∈ V, 2 := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      exact curve_pairCount_le_two hF u v (hU u hu) (hV v hv) z hz
    _ = _ := by simp; ring


lemma curve_intersection {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    {z : F × F} (hzu : z ∈ curve u) (hzv : z ∈ curve v) : z = 0 := by
  rw [mem_curve] at hzu hzv
  have hx : z.1 = 0 := by
    by_contra h
    have hm := (div_eq_div_iff hu hv).mp (hzu.symm.trans hzv)
    exact huv ((mul_left_cancel₀ (pow_ne_zero 2 h) hm).symm)
  have hy : z.2 = 0 := by simpa [hx] using hzu
  exact Prod.ext hx hy

lemma neg_mem_curve (w : F) {z : F × F} (hz : z ∈ curve w) : -z ∈ curve (-w) := by
  simpa only [mem_curve, Prod.snd_neg, Prod.fst_neg, neg_sq, div_neg, neg_inj] using hz

noncomputable def partialCurve (w : F) (T : Finset F) : Finset (F × F) :=
  T.image (fun x ↦ (x, x ^ 2 / w))

noncomputable def repairPoints (w : F) (T : Finset F) : Finset (F × F) :=
  partialCurve w T ∪ (partialCurve w T).image Neg.neg

lemma partialCurve_subset (w : F) (T : Finset F) : partialCurve w T ⊆ curve w :=
  Finset.image_subset_image (Finset.subset_univ _)

lemma repairPoints_symmetric (w : F) (T : Finset F) :
    ∀ z ∈ repairPoints w T, -z ∈ repairPoints w T := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_union_left _ (by simpa only [neg_neg] using hx)

lemma repairPoints_zero_notMem (w : F) (T : Finset F) (hT : (0 : F) ∉ T) :
    (0 : F × F) ∉ repairPoints w T := by
  have h0 : (0 : F × F) ∉ partialCurve w T := by
    rintro hz
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hz
    have hh : x = 0 := congrArg Prod.fst he
    exact hT (hh ▸ hx)
  intro hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact h0 hz
  · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hz
    exact h0 ((neg_eq_zero.mp he) ▸ hx)

lemma repairPoints_subset (w : F) (T : Finset F) :
    repairPoints w T ⊆ parabolaSet {w, -w} := by
  intro z hz
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases Finset.mem_union.mp hz with hz | hz
  · exact ⟨w, by simp, (mem_curve _ _).mp (partialCurve_subset w T hz)⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨-w, by simp, (mem_curve _ _).mp (neg_mem_curve w (partialCurve_subset w T hx))⟩

lemma parameter_ne_neg (hF : ringChar F ≠ 2) {w : F} (hw : w ≠ 0) : w ≠ -w := by
  intro he
  have hh : (2 : F) * w = 0 := by linear_combination he
  exact mul_ne_zero (Ring.two_ne_zero hF) hw hh

lemma repairPoints_card (hF : ringChar F ≠ 2) (w : F) (hw : w ≠ 0)
    (T : Finset F) (hT : (0 : F) ∉ T) : (repairPoints w T).card = 2 * T.card := by
  have hdis : Disjoint (partialCurve w T) ((partialCurve w T).image Neg.neg) := by
    apply Finset.disjoint_left.mpr
    intro z hz hnz
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hnz
    have hc : z ∈ curve (-w) := he ▸ neg_mem_curve w (partialCurve_subset w T hx)
    have hz0 := curve_intersection hw (neg_ne_zero.mpr hw) (parameter_ne_neg hF hw)
      (partialCurve_subset w T hz) hc
    exact repairPoints_zero_notMem w T hT (hz0 ▸ Finset.mem_union_left _ hz)
  rw [repairPoints, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ neg_injective,
    partialCurve, Finset.card_image_of_injective _ (fun _ _ he ↦ congrArg Prod.fst he)]
  omega

lemma repairPoints_disjoint (U : Finset F) (hU : ∀ u ∈ U, u ≠ 0)
    (w : F) (hw : w ≠ 0) (hwU : w ∉ U) (hnwU : -w ∉ U)
    (T : Finset F) (hT : (0 : F) ∉ T) :
    Disjoint (parabolaSet U) (repairPoints w T) := by
  apply Finset.disjoint_left.mpr
  intro z hz hzd
  obtain ⟨u, hu, hzu⟩ := (Finset.mem_filter.mp hz).2
  obtain ⟨v, hv, hzv⟩ := (Finset.mem_filter.mp (repairPoints_subset w T hzd)).2
  have hv0 : v ≠ 0 := by
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hw
    · rw [Finset.mem_singleton.mp hv]
      exact neg_ne_zero.mpr hw
  have huv : u ≠ v := by
    intro he
    subst u
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hwU hu
    · exact hnwU ((Finset.mem_singleton.mp hv) ▸ hu)
  have hz0 := curve_intersection (hU u hu) hv0 huv
    ((mem_curve u z).mpr hzu) ((mem_curve v z).mpr hzv)
  exact repairPoints_zero_notMem w T hT (hz0 ▸ hzd)

lemma disjoint_symmetric_origin {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A D : Finset G) (hdis : Disjoint A D) (hneg : ∀ x ∈ D, -x ∈ D) :
    pairCount D A 0 = 0 := by
  rw [pairCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hn
  exact Finset.disjoint_left.mp hdis (by simpa only [zero_sub] using hn) (hneg x hx)

/-- Adding a symmetric piece of two unused parabolas repairs the origin while
changing any other representation count by at most `8|U|+8`. -/
lemma parabola_origin_repair (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0) (hne : U.Nonempty)
    (w : F) (hw : w ≠ 0) (hwU : w ∉ U) (hnwU : -w ∉ U)
    (T : Finset F) (hT : (0 : F) ∉ T) :
    pairCount (parabolaSet U ∪ repairPoints w T)
        (parabolaSet U ∪ repairPoints w T) 0 = 1 + 2 * T.card ∧
      ∀ z : F × F, z ≠ 0 →
        pairCount (parabolaSet U) (parabolaSet U) z ≤
          pairCount (parabolaSet U ∪ repairPoints w T) (parabolaSet U ∪ repairPoints w T) z ∧
        pairCount (parabolaSet U ∪ repairPoints w T) (parabolaSet U ∪ repairPoints w T) z ≤
          pairCount (parabolaSet U) (parabolaSet U) z + 8 * U.card + 8 := by
  have hd := repairPoints_disjoint U hU w hw hwU hnwU T hT
  have hneg := repairPoints_symmetric w T
  have hV : ∀ v ∈ ({w, -w} : Finset F), v ≠ 0 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hw
    · exact neg_ne_zero.mpr hw
  have hVcard : ({w, -w} : Finset F).card = 2 := by simp [parameter_ne_neg hF hw]
  have hzA : pairCount (parabolaSet U) (parabolaSet U) 0 = 1 :=
    parabolaSet_origin_count U hU hUU hne
  constructor
  · rw [pairCount_union_self _ _ _ hd, hzA,
      disjoint_symmetric_origin _ _ hd hneg, symmetric_origin _ hneg,
      repairPoints_card hF w hw T hT]
  · intro z hz
    have hm := (pairCount_mono (repairPoints_subset w T) (Finset.Subset.refl _) z).trans
      (parabolaSet_pairCount_le hF {w, -w} U hV hU z hz)
    have hs := (pairCount_mono (repairPoints_subset w T) (repairPoints_subset w T) z).trans
      (parabolaSet_pairCount_le hF {w, -w} {w, -w} hV hV z hz)
    rw [hVcard] at hm hs
    rw [pairCount_union_self _ _ _ hd]
    constructor <;> omega


lemma exists_unused_parameter (U : Finset F) (hcard : 2 * U.card + 1 < Fintype.card F) :
    ∃ w : F, w ≠ 0 ∧ w ∉ U ∧ -w ∉ U := by
  let bad := insert 0 (U ∪ U.image Neg.neg)
  have hbad : bad.card ≤ 2 * U.card + 1 := by
    have h₁ := Finset.card_insert_le (0 : F) (U ∪ U.image Neg.neg)
    have h₂ := Finset.card_union_le U (U.image Neg.neg)
    have h₃ : (U.image Neg.neg).card ≤ U.card := Finset.card_image_le
    dsimp only [bad]
    omega
  have hnot : ¬(Finset.univ : Finset F) ⊆ bad := by
    intro hh
    have hc := Finset.card_le_card hh
    rw [Finset.card_univ] at hc
    omega
  obtain ⟨w, _, hw⟩ := Finset.not_subset.mp hnot
  have hw0 : w ≠ 0 := by
    intro h
    exact hw (Finset.mem_insert.mpr (Or.inl h))
  have hwU : w ∉ U := by
    intro h
    exact hw (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
  have hnwU : -w ∉ U := by
    intro h
    exact hw (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨-w, h, neg_neg w⟩)))
  exact ⟨w, hw0, hwU, hnwU⟩

/-- Existence of a partial-parabola origin repair in a sufficiently large field. -/
theorem exists_parabola_origin_repair (hF : ringChar F ≠ 2) (U : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0) (hne : U.Nonempty)
    (hcard : 2 * U.card + 1 < Fintype.card F) (m : ℕ) (hm : m < Fintype.card F) :
    ∃ B : Finset (F × F), pairCount B B 0 = 1 + 2 * m ∧
      ∀ z : F × F, z ≠ 0 →
        pairCount (parabolaSet U) (parabolaSet U) z ≤ pairCount B B z ∧
        pairCount B B z ≤ pairCount (parabolaSet U) (parabolaSet U) z + 8 * U.card + 8 := by
  obtain ⟨w, hw, hwU, hnwU⟩ := exists_unused_parameter U hcard
  have hTcard : m ≤ ((Finset.univ : Finset F).erase 0).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨T, hTsub, hTm⟩ := Finset.exists_subset_card_eq hTcard
  have hT0 : (0 : F) ∉ T := fun hh ↦ (Finset.mem_erase.mp (hTsub hh)).1 rfl
  obtain ⟨hzero, hnonzero⟩ := parabola_origin_repair hF U hU hUU hne w hw hwU hnwU T hT0
  exact ⟨parabolaSet U ∪ repairPoints w T, by simpa only [hTm] using hzero, hnonzero⟩

end Erdos66ParabolaRepair
