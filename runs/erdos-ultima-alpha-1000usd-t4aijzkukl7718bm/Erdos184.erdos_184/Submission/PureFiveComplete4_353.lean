import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3530 : ∀ i : Fin 200, Compatible (706000 + i.val) →
    (table.lookup (706000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3530 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 706000 706200 :=
  FiniteIntervals.of_fin 706000 200 complete_chunk3530

lemma complete_chunk3531 : ∀ i : Fin 200, Compatible (706200 + i.val) →
    (table.lookup (706200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3531 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 706200 706400 :=
  FiniteIntervals.of_fin 706200 200 complete_chunk3531

lemma complete_chunk3532 : ∀ i : Fin 200, Compatible (706400 + i.val) →
    (table.lookup (706400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3532 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 706400 706600 :=
  FiniteIntervals.of_fin 706400 200 complete_chunk3532

lemma complete_chunk3533 : ∀ i : Fin 200, Compatible (706600 + i.val) →
    (table.lookup (706600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3533 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 706600 706800 :=
  FiniteIntervals.of_fin 706600 200 complete_chunk3533

lemma complete_chunk3534 : ∀ i : Fin 200, Compatible (706800 + i.val) →
    (table.lookup (706800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3534 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 706800 707000 :=
  FiniteIntervals.of_fin 706800 200 complete_chunk3534

lemma complete_chunk3535 : ∀ i : Fin 200, Compatible (707000 + i.val) →
    (table.lookup (707000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3535 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 707000 707200 :=
  FiniteIntervals.of_fin 707000 200 complete_chunk3535

lemma complete_chunk3536 : ∀ i : Fin 200, Compatible (707200 + i.val) →
    (table.lookup (707200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3536 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 707200 707400 :=
  FiniteIntervals.of_fin 707200 200 complete_chunk3536

lemma complete_chunk3537 : ∀ i : Fin 200, Compatible (707400 + i.val) →
    (table.lookup (707400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3537 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 707400 707600 :=
  FiniteIntervals.of_fin 707400 200 complete_chunk3537

lemma complete_chunk3538 : ∀ i : Fin 200, Compatible (707600 + i.val) →
    (table.lookup (707600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3538 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 707600 707800 :=
  FiniteIntervals.of_fin 707600 200 complete_chunk3538

lemma complete_chunk3539 : ∀ i : Fin 200, Compatible (707800 + i.val) →
    (table.lookup (707800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3539 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 707800 708000 :=
  FiniteIntervals.of_fin 707800 200 complete_chunk3539

#print axioms interval_chunk3530
end Erdos184Work.PureFiveFilter4
