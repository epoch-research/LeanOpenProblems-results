import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5450 : ∀ i : Fin 200, Compatible (1090000 + i.val) →
    (table.lookup (1090000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5450 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1090000 1090200 :=
  FiniteIntervals.of_fin 1090000 200 complete_chunk5450

lemma complete_chunk5451 : ∀ i : Fin 200, Compatible (1090200 + i.val) →
    (table.lookup (1090200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5451 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1090200 1090400 :=
  FiniteIntervals.of_fin 1090200 200 complete_chunk5451

lemma complete_chunk5452 : ∀ i : Fin 200, Compatible (1090400 + i.val) →
    (table.lookup (1090400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5452 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1090400 1090600 :=
  FiniteIntervals.of_fin 1090400 200 complete_chunk5452

lemma complete_chunk5453 : ∀ i : Fin 200, Compatible (1090600 + i.val) →
    (table.lookup (1090600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5453 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1090600 1090800 :=
  FiniteIntervals.of_fin 1090600 200 complete_chunk5453

lemma complete_chunk5454 : ∀ i : Fin 200, Compatible (1090800 + i.val) →
    (table.lookup (1090800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5454 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1090800 1091000 :=
  FiniteIntervals.of_fin 1090800 200 complete_chunk5454

lemma complete_chunk5455 : ∀ i : Fin 200, Compatible (1091000 + i.val) →
    (table.lookup (1091000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5455 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1091000 1091200 :=
  FiniteIntervals.of_fin 1091000 200 complete_chunk5455

lemma complete_chunk5456 : ∀ i : Fin 200, Compatible (1091200 + i.val) →
    (table.lookup (1091200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5456 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1091200 1091400 :=
  FiniteIntervals.of_fin 1091200 200 complete_chunk5456

lemma complete_chunk5457 : ∀ i : Fin 200, Compatible (1091400 + i.val) →
    (table.lookup (1091400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5457 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1091400 1091600 :=
  FiniteIntervals.of_fin 1091400 200 complete_chunk5457

lemma complete_chunk5458 : ∀ i : Fin 200, Compatible (1091600 + i.val) →
    (table.lookup (1091600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5458 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1091600 1091800 :=
  FiniteIntervals.of_fin 1091600 200 complete_chunk5458

lemma complete_chunk5459 : ∀ i : Fin 200, Compatible (1091800 + i.val) →
    (table.lookup (1091800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5459 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1091800 1092000 :=
  FiniteIntervals.of_fin 1091800 200 complete_chunk5459

#print axioms interval_chunk5450
end Erdos184Work.PureFiveFilter4
