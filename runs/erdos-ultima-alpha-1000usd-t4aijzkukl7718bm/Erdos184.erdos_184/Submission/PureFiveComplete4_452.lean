import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4520 : ∀ i : Fin 200, Compatible (904000 + i.val) →
    (table.lookup (904000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4520 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 904000 904200 :=
  FiniteIntervals.of_fin 904000 200 complete_chunk4520

lemma complete_chunk4521 : ∀ i : Fin 200, Compatible (904200 + i.val) →
    (table.lookup (904200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4521 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 904200 904400 :=
  FiniteIntervals.of_fin 904200 200 complete_chunk4521

lemma complete_chunk4522 : ∀ i : Fin 200, Compatible (904400 + i.val) →
    (table.lookup (904400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4522 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 904400 904600 :=
  FiniteIntervals.of_fin 904400 200 complete_chunk4522

lemma complete_chunk4523 : ∀ i : Fin 200, Compatible (904600 + i.val) →
    (table.lookup (904600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4523 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 904600 904800 :=
  FiniteIntervals.of_fin 904600 200 complete_chunk4523

lemma complete_chunk4524 : ∀ i : Fin 200, Compatible (904800 + i.val) →
    (table.lookup (904800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4524 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 904800 905000 :=
  FiniteIntervals.of_fin 904800 200 complete_chunk4524

lemma complete_chunk4525 : ∀ i : Fin 200, Compatible (905000 + i.val) →
    (table.lookup (905000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4525 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 905000 905200 :=
  FiniteIntervals.of_fin 905000 200 complete_chunk4525

lemma complete_chunk4526 : ∀ i : Fin 200, Compatible (905200 + i.val) →
    (table.lookup (905200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4526 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 905200 905400 :=
  FiniteIntervals.of_fin 905200 200 complete_chunk4526

lemma complete_chunk4527 : ∀ i : Fin 200, Compatible (905400 + i.val) →
    (table.lookup (905400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4527 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 905400 905600 :=
  FiniteIntervals.of_fin 905400 200 complete_chunk4527

lemma complete_chunk4528 : ∀ i : Fin 200, Compatible (905600 + i.val) →
    (table.lookup (905600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4528 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 905600 905800 :=
  FiniteIntervals.of_fin 905600 200 complete_chunk4528

lemma complete_chunk4529 : ∀ i : Fin 200, Compatible (905800 + i.val) →
    (table.lookup (905800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4529 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 905800 906000 :=
  FiniteIntervals.of_fin 905800 200 complete_chunk4529

#print axioms interval_chunk4520
end Erdos184Work.PureFiveFilter4
