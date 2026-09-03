import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3550 : ∀ i : Fin 200, Compatible (710000 + i.val) →
    (table.lookup (710000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3550 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 710000 710200 :=
  FiniteIntervals.of_fin 710000 200 complete_chunk3550

lemma complete_chunk3551 : ∀ i : Fin 200, Compatible (710200 + i.val) →
    (table.lookup (710200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3551 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 710200 710400 :=
  FiniteIntervals.of_fin 710200 200 complete_chunk3551

lemma complete_chunk3552 : ∀ i : Fin 200, Compatible (710400 + i.val) →
    (table.lookup (710400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3552 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 710400 710600 :=
  FiniteIntervals.of_fin 710400 200 complete_chunk3552

lemma complete_chunk3553 : ∀ i : Fin 200, Compatible (710600 + i.val) →
    (table.lookup (710600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3553 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 710600 710800 :=
  FiniteIntervals.of_fin 710600 200 complete_chunk3553

lemma complete_chunk3554 : ∀ i : Fin 200, Compatible (710800 + i.val) →
    (table.lookup (710800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3554 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 710800 711000 :=
  FiniteIntervals.of_fin 710800 200 complete_chunk3554

lemma complete_chunk3555 : ∀ i : Fin 200, Compatible (711000 + i.val) →
    (table.lookup (711000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3555 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 711000 711200 :=
  FiniteIntervals.of_fin 711000 200 complete_chunk3555

lemma complete_chunk3556 : ∀ i : Fin 200, Compatible (711200 + i.val) →
    (table.lookup (711200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3556 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 711200 711400 :=
  FiniteIntervals.of_fin 711200 200 complete_chunk3556

lemma complete_chunk3557 : ∀ i : Fin 200, Compatible (711400 + i.val) →
    (table.lookup (711400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3557 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 711400 711600 :=
  FiniteIntervals.of_fin 711400 200 complete_chunk3557

lemma complete_chunk3558 : ∀ i : Fin 200, Compatible (711600 + i.val) →
    (table.lookup (711600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3558 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 711600 711800 :=
  FiniteIntervals.of_fin 711600 200 complete_chunk3558

lemma complete_chunk3559 : ∀ i : Fin 200, Compatible (711800 + i.val) →
    (table.lookup (711800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3559 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 711800 712000 :=
  FiniteIntervals.of_fin 711800 200 complete_chunk3559

#print axioms interval_chunk3550
end Erdos184Work.PureFiveFilter4
