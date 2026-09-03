import Submission.InterceptCollisionIncidenceExplore

/-! Counting distinct unoriented edge triples, with the cardinality cost of
both orientations kept explicit. -/
namespace Erdos66EdgeTripleBudget
open Erdos66InterceptEdgePolynomial Erdos66InterceptCollisionIncidence
open scoped Classical
set_option maxHeartbeats 1800000
variable {α : Type*}

def Valid (e f g : α × α) : Prop :=
  ¬SameEdge e f ∧ ¬SameEdge f g ∧ ¬SameEdge g e

noncomputable def tripleMass (R : Finset (α × α)) : ℕ :=
  ∑ e ∈ R, ∑ f ∈ R, ∑ g ∈ R, if Valid e f g then 1 else 0

lemma sameEdge_class_card (R : Finset (α × α)) (e : α × α) :
    (R.filter (fun f ↦ SameEdge e f)).card ≤ 2 := by
  have hs : R.filter (fun f ↦ SameEdge e f) ⊆ {e,e.swap} := by
    intro f hf
    rcases (Finset.mem_filter.mp hf).2 with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · have hh : f=e := Prod.ext h1.symm h2.symm
      simp [hh]
    · have hh : f=e.swap := Prod.ext h2.symm h1.symm
      simp [hh]
  exact (Finset.card_le_card hs).trans Finset.card_le_two

lemma different_class_card (R : Finset (α × α)) (e : α × α) :
    R.card-2 ≤ (R.filter (fun f ↦ ¬SameEdge e f)).card := by
  have he := sameEdge_class_card R e
  have hh := @Finset.card_filter_add_card_filter_not _ R (fun f ↦ SameEdge e f) _ _
  omega

lemma different_two_classes_card (R : Finset (α × α)) (e f : α × α) :
    R.card-4 ≤ (R.filter (fun g ↦ ¬SameEdge f g ∧ ¬SameEdge g e)).card := by
  have hs : R.filter (fun g ↦ SameEdge f g ∨ SameEdge g e) ⊆
      R.filter (fun g ↦ SameEdge f g) ∪ R.filter (fun g ↦ SameEdge e g) := by
    intro g hg
    obtain ⟨hg,h⟩ := Finset.mem_filter.mp hg
    rcases h with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hg,sameEdge_symm g e h⟩)
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have he := sameEdge_class_card R e
  have hf := sameEdge_class_card R f
  have hh := @Finset.card_filter_add_card_filter_not _ R
    (fun g ↦ SameEdge f g ∨ SameEdge g e) _ _
  simp only [not_or] at hh
  omega

lemma tripleMass_eq (R : Finset (α × α)) :
    tripleMass R = ∑ e ∈ R, ∑ f ∈ R with ¬SameEdge e f,
      (R.filter (fun g ↦ ¬SameEdge f g ∧ ¬SameEdge g e)).card := by
  unfold tripleMass
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hef : SameEdge e f
  · simp [Valid,hef]
  · simp only [hef,not_false_eq_true,if_true,Finset.card_filter,Valid,true_and]

lemma tripleMass_lower (R : Finset (α × α)) :
    (R.card-4)^3 ≤ tripleMass R := by
  rw [tripleMass_eq]
  have h1 : ∀ e, (R.card-2)*(R.card-4) ≤
      ∑ f ∈ R with ¬SameEdge e f,
        (R.filter (fun g ↦ ¬SameEdge f g ∧ ¬SameEdge g e)).card := by
    intro e
    calc
      _ ≤ (R.filter (fun f ↦ ¬SameEdge e f)).card*(R.card-4) :=
        Nat.mul_le_mul_right _ (different_class_card R e)
      _ = ∑ _f ∈ R with ¬SameEdge e _f, (R.card-4) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun f _ ↦ different_two_classes_card R e f)
  have h2 : R.card*((R.card-2)*(R.card-4)) ≤
      ∑ e ∈ R, ∑ f ∈ R with ¬SameEdge e f,
        (R.filter (fun g ↦ ¬SameEdge f g ∧ ¬SameEdge g e)).card := by
    calc
      _ = ∑ _e ∈ R, (R.card-2)*(R.card-4) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun e _ ↦ h1 e)
  apply le_trans _ h2
  calc
    (R.card-4)^3 = (R.card-4)*((R.card-4)*(R.card-4)) := by ring
    _ ≤ R.card*((R.card-2)*(R.card-4)) :=
      Nat.mul_le_mul (Nat.sub_le _ _) (Nat.mul_le_mul_right _ (by omega))

end Erdos66EdgeTripleBudget
