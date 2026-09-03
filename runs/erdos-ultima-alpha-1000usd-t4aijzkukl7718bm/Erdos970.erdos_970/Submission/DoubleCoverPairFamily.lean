import Submission.DoubleCoverSelectedPairs

/-! Exact masses and cardinality bounds for a selected family of prime pairs. -/
namespace Erdos970.DoubleCover
open Finset

lemma pair_mass_formula (H : Finset ℕ) (w : ℕ → ℝ) :
    (∑ T ∈ H.powersetCard 2, ∏ p ∈ T, w p) =
      ((∑ p ∈ H, w p) ^ 2 - ∑ p ∈ H, (w p) ^ 2) / 2 := by
  classical
  induction H using Finset.induction_on with
  | empty =>
    rw [powersetCard_eq_empty.mpr (by simp)]
    simp
  | @insert a H ha ih =>
    have hd : Disjoint (H.powersetCard 2) ((H.powersetCard 1).image (insert a)) := by
      apply disjoint_left.mpr
      intro T hT hTi
      obtain ⟨U, hU, rfl⟩ := mem_image.mp hTi
      exact ha ((mem_powersetCard.mp hT).1 (mem_insert_self _ _))
    have hi : Set.InjOn (insert a) (↑(H.powersetCard 1) : Set (Finset ℕ)) := by
      intro U hU V hV hUV
      have hau : a ∉ U := fun hh => ha ((mem_powersetCard.mp hU).1 hh)
      have hav : a ∉ V := fun hh => ha ((mem_powersetCard.mp hV).1 hh)
      simpa only [erase_insert hau, erase_insert hav] using congrArg (fun T => T.erase a) hUV
    rw [show 2 = 1 + 1 by omega, powersetCard_succ_insert ha 1, sum_union hd,
      sum_image hi]
    have he : (∑ T ∈ H.powersetCard 1, ∏ p ∈ insert a T, w p) =
        w a * ∑ p ∈ H, w p := by
      rw [powersetCard_one, sum_map, mul_sum]
      apply sum_congr rfl
      intro p hp
      simp [prod_pair (show a ≠ p from fun hh => ha (hh ▸ hp))]
    rw [he, ih, sum_insert ha, sum_insert ha]
    ring

noncomputable def selectedPairFamily (H A C : Finset ℕ) : Finset (Finset ℕ) :=
  H.powersetCard 2 ∪ (A ×ˢ C).image (fun z => {z.1, z.2})

lemma cross_pair_injective (A C : Finset ℕ) (hd : Disjoint A C) :
    Set.InjOn (fun z : ℕ × ℕ => ({z.1, z.2} : Finset ℕ)) (↑(A ×ˢ C) : Set (ℕ × ℕ)) := by
  intro u hu v hv huv
  change ({u.1, u.2} : Finset ℕ) = {v.1, v.2} at huv
  obtain ⟨huA, huC⟩ := mem_product.mp hu
  obtain ⟨hvA, hvC⟩ := mem_product.mp hv
  have he1 : u.1 = v.1 := by
    have hm : u.1 ∈ ({v.1, v.2} : Finset ℕ) := by rw [← huv]; exact mem_insert_self _ _
    rcases mem_insert.mp hm with hh | hh
    · exact hh
    · exact False.elim ((disjoint_left.mp hd) huA ((mem_singleton.mp hh) ▸ hvC))
  have he2 : u.2 = v.2 := by
    have hm : u.2 ∈ ({v.1, v.2} : Finset ℕ) := by rw [← huv]; exact mem_insert_of_mem (mem_singleton_self _)
    rcases mem_insert.mp hm with hh | hh
    · exact False.elim ((disjoint_left.mp hd) hvA (hh ▸ huC))
    · exact mem_singleton.mp hh
  exact Prod.ext he1 he2

lemma selectedPairFamily_disjoint (H A C : Finset ℕ) (hC : Disjoint H C) :
    Disjoint (H.powersetCard 2) ((A ×ˢ C).image (fun z => ({z.1, z.2} : Finset ℕ))) := by
  apply disjoint_left.mpr
  intro T hT hTi
  obtain ⟨⟨a,c⟩, hac, rfl⟩ := mem_image.mp hTi
  exact (disjoint_left.mp hC) ((mem_powersetCard.mp hT).1 (by simp))
    (mem_product.mp hac).2

lemma selectedPairFamily_subset (R H A C : Finset ℕ)
    (hH : H ⊆ R) (hA : A ⊆ H) (hC : C ⊆ R) (hd : Disjoint H C) :
    selectedPairFamily H A C ⊆ R.powersetCard 2 := by
  intro T hT
  rcases mem_union.mp hT with hT | hT
  · obtain ⟨hTH, hcard⟩ := mem_powersetCard.mp hT
    exact mem_powersetCard.mpr ⟨hTH.trans hH, hcard⟩
  · obtain ⟨⟨a,c⟩, hac, rfl⟩ := mem_image.mp hT
    obtain ⟨ha,hc⟩ := mem_product.mp hac
    have hne : a ≠ c := fun hh => (disjoint_left.mp hd) (hA ha) (hh ▸ hc)
    exact mem_powersetCard.mpr ⟨by simp [insert_subset_iff, hH (hA ha), hC hc], by simp [hne]⟩

lemma selectedPairFamily_mass (H A C : Finset ℕ) (hA : A ⊆ H)
    (hd : Disjoint H C) (w : ℕ → ℝ) :
    (∑ T ∈ selectedPairFamily H A C, ∏ p ∈ T, w p) =
      ((∑ p ∈ H, w p) ^ 2 - ∑ p ∈ H, (w p) ^ 2) / 2 +
        (∑ p ∈ A, w p) * (∑ p ∈ C, w p) := by
  classical
  rw [selectedPairFamily, sum_union (selectedPairFamily_disjoint H A C hd),
    pair_mass_formula, sum_image (cross_pair_injective A C (hd.mono_left hA)), sum_product,
    sum_mul_sum]
  congr 1
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro c hc
  change (∏ p ∈ ({a, c} : Finset ℕ), w p) = w a * w c
  exact prod_pair (fun hh => (disjoint_left.mp hd) (hA ha) (hh.symm ▸ hc))

lemma selectedPairFamily_card_le (H A C : Finset ℕ) :
    ((selectedPairFamily H A C).card : ℝ) ≤
      (H.card : ℝ) ^ 2 / 2 + (A.card : ℝ) * C.card := by
  have h := (card_union_le (H.powersetCard 2)
    ((A ×ˢ C).image (fun z => ({z.1, z.2} : Finset ℕ)))).trans
      (Nat.add_le_add_left card_image_le _)
  rw [card_powersetCard, card_product] at h
  have hp : (H.card.choose 2 : ℝ) ≤ (H.card : ℝ) ^ 2 / 2 := by
    have he := Nat.choose_two_right H.card
    have hi : 2 * H.card.choose 2 ≤ H.card * H.card := by
      rw [he]
      exact (Nat.mul_div_le _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have hr : 2 * (H.card.choose 2 : ℝ) ≤ (H.card : ℝ) * H.card := by exact_mod_cast hi
    nlinarith only [hr]
  have hr : ((selectedPairFamily H A C).card : ℝ) ≤
      (H.card.choose 2 : ℝ) + (A.card : ℝ) * C.card := by exact_mod_cast h
  linarith

#print axioms selectedPairFamily_mass
#print axioms selectedPairFamily_card_le
end Erdos970.DoubleCover
