import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3630 : ∀ i : Fin 200, Compatible (726000 + i.val) →
    (table.lookup (726000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3630 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 726000 726200 :=
  FiniteIntervals.of_fin 726000 200 complete_chunk3630

lemma complete_chunk3631 : ∀ i : Fin 200, Compatible (726200 + i.val) →
    (table.lookup (726200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3631 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 726200 726400 :=
  FiniteIntervals.of_fin 726200 200 complete_chunk3631

lemma complete_chunk3632 : ∀ i : Fin 200, Compatible (726400 + i.val) →
    (table.lookup (726400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3632 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 726400 726600 :=
  FiniteIntervals.of_fin 726400 200 complete_chunk3632

lemma complete_chunk3633 : ∀ i : Fin 200, Compatible (726600 + i.val) →
    (table.lookup (726600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3633 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 726600 726800 :=
  FiniteIntervals.of_fin 726600 200 complete_chunk3633

lemma complete_chunk3634 : ∀ i : Fin 200, Compatible (726800 + i.val) →
    (table.lookup (726800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3634 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 726800 727000 :=
  FiniteIntervals.of_fin 726800 200 complete_chunk3634

lemma complete_chunk3635 : ∀ i : Fin 200, Compatible (727000 + i.val) →
    (table.lookup (727000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3635 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 727000 727200 :=
  FiniteIntervals.of_fin 727000 200 complete_chunk3635

lemma complete_chunk3636 : ∀ i : Fin 200, Compatible (727200 + i.val) →
    (table.lookup (727200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3636 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 727200 727400 :=
  FiniteIntervals.of_fin 727200 200 complete_chunk3636

lemma complete_chunk3637 : ∀ i : Fin 200, Compatible (727400 + i.val) →
    (table.lookup (727400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3637 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 727400 727600 :=
  FiniteIntervals.of_fin 727400 200 complete_chunk3637

lemma complete_chunk3638 : ∀ i : Fin 200, Compatible (727600 + i.val) →
    (table.lookup (727600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3638 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 727600 727800 :=
  FiniteIntervals.of_fin 727600 200 complete_chunk3638

lemma complete_chunk3639 : ∀ i : Fin 200, Compatible (727800 + i.val) →
    (table.lookup (727800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3639 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 727800 728000 :=
  FiniteIntervals.of_fin 727800 200 complete_chunk3639

#print axioms interval_chunk3630
end Erdos184Work.PureFiveFilter4
