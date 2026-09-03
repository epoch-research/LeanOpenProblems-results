import Submission.CollisionBounds

/-!
An additive translate of a set of square values can also consist of squares,
but a fixed nonzero translate has only subpowerly many simultaneous square
values at root height N. This restricts the translated-fiber overlap example,
not general partial-fiber compatibility or nonuniform selection.
-/
namespace Erdos773.TranslatedSquareFibers
open Finset

/-- A Sidon subset of a set and its positive translate can double at most
one original position. This applies to arbitrary natural-value sets. -/
theorem sidon_in_translate_union {A S : Finset ℕ} {C : ℕ} (hC : 0 < C)
    (hsub : S ⊆ A ∪ A.image (fun a => a+C)) (hS : IsSidon (S : Set ℕ)) :
    S.card ≤ A.card+1 := by
  let X := A ∩ S
  let Y := A.filter (fun a => a+C ∈ S)
  have hcover : S ⊆ X ∪ Y.image (fun a => a+C) := by
    intro a ha
    rcases mem_union.mp (hsub ha) with hA | hA
    · exact mem_union_left _ (mem_inter.mpr ⟨hA,ha⟩)
    · obtain ⟨b,hb,rfl⟩ := mem_image.mp hA
      exact mem_union_right _ (mem_image.mpr ⟨b,mem_filter.mpr ⟨hb,ha⟩,rfl⟩)
  have hdouble : (X ∩ Y).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨haX,haY⟩ := mem_inter.mp ha
    obtain ⟨hbX,hbY⟩ := mem_inter.mp hb
    have haS := (mem_inter.mp haX).2
    have hbS := (mem_inter.mp hbX).2
    have haC := (mem_filter.mp haY).2
    have hbC := (mem_filter.mp hbY).2
    rcases hS a haS (a+C) haC (b+C) hbC b hbS (by omega) with h | h <;> omega
  have hxy : X ∪ Y ⊆ A := by
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact (mem_inter.mp ha).1
    · exact (mem_filter.mp ha).1
  have hi : (Y.image (fun a => a+C)).card=Y.card :=
    card_image_of_injective Y (fun a b h => Nat.add_right_cancel h)
  have hc := (card_le_card hcover).trans (card_union_le X (Y.image (fun a => a+C)))
  rw [hi] at hc
  have hh := card_union_add_card_inter X Y
  have hb := card_le_card hxy
  omega

/-- This is an upper bound for the translated union only, not for all squares
up to the same height. -/
theorem max_translate_union (A : Finset ℕ) (C : ℕ) (hC : 0 < C) :
    maxSidonSubsetCard (A ∪ A.image (fun a => a+C)) ≤ A.card+1 := by
  apply Finset.sup_le
  intro S hS
  obtain ⟨hsub,hSidon⟩ := mem_filter.mp hS
  exact sidon_in_translate_union hC (mem_powerset.mp hsub) hSidon

/-- Values that are squares and remain squares after adding C. -/
def commonValues (N C : ℕ) : Finset ℕ :=
  ((Icc 1 N).image (fun n => n^2)).filter
    (fun a => a+C ∈ (Icc 1 N).image (fun n => n^2))

lemma commonValues_eq (N C : ℕ) (hC : 0 < C) :
    commonValues N C=(squareDifferenceReps N C).image (fun ab => ab.1^2) := by
  ext a
  simp only [commonValues, mem_filter, mem_image, squareDifferenceReps, mem_product]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,y,hy,he⟩
    have hxy : x < y := by nlinarith only [he,hC]
    exact ⟨(x,y),⟨⟨hx,hy⟩,hxy,he⟩,rfl⟩
  · rintro ⟨⟨x,y⟩,⟨⟨hx,hy⟩,hxy,he⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,y,hy,he⟩

theorem card_le_representations (N C : ℕ) (hC : 0 < C) :
    (commonValues N C).card ≤ (squareDifferenceReps N C).card := by
  rw [commonValues_eq N C hC]
  exact card_image_le

/-- Uniform over all positive translates, including translates too large
to have any common values. -/
theorem commonValues_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ K > (0 : ℝ), ∀ N C : ℕ, 0 < C →
      ((commonValues N C).card : ℝ) ≤ K*(N : ℝ)^δ := by
  obtain ⟨K,hK,hbound⟩ := squareDifferenceReps_subpower (δ/2) (by linarith)
  refine ⟨K,hK,?_⟩
  intro N C hC
  by_cases hc : C ≤ N^2
  · have h1 : ((commonValues N C).card : ℝ) ≤ (squareDifferenceReps N C).card := by
      exact_mod_cast card_le_representations N C hC
    have h2 := hbound N C hC hc
    have he : 2*(δ/2)=δ := by ring
    rw [he] at h2
    exact h1.trans h2
  · have he : commonValues N C=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨_,hb⟩ := mem_filter.mp ha
      obtain ⟨b,hb,he⟩ := mem_image.mp hb
      have hsq := Nat.pow_le_pow_left (mem_Icc.mp hb).2 2
      omega
    rw [he, card_empty, Nat.cast_zero]
    positivity

/-- A square fiber and any nonzero positive translate of it cannot both have
near-linear size at a common root height. No Sidon hypothesis is needed. -/
theorem translated_fiber_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ K > (0 : ℝ), ∀ N C : ℕ, ∀ A : Finset ℕ, 0 < C →
      A ⊆ (Icc 1 N).image (fun n => n^2) →
      (∀ a ∈ A, a+C ∈ (Icc 1 N).image (fun n => n^2)) →
      (A.card : ℝ) ≤ K*(N : ℝ)^δ := by
  obtain ⟨K,hK,hbound⟩ := commonValues_subpower δ hδ
  refine ⟨K,hK,?_⟩
  intro N C A hC hA hshift
  have hsub : A ⊆ commonValues N C := by
    intro a ha
    exact mem_filter.mpr ⟨hA ha,hshift a ha⟩
  have hc : (A.card : ℝ) ≤ (commonValues N C).card := by
    exact_mod_cast card_le_card hsub
  exact hc.trans (hbound N C hC)

#print axioms max_translate_union
#print axioms commonValues_subpower
#print axioms translated_fiber_subpower
end Erdos773.TranslatedSquareFibers
