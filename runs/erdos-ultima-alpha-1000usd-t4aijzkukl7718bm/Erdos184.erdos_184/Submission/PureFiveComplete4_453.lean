import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4530 : ∀ i : Fin 200, Compatible (906000 + i.val) →
    (table.lookup (906000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4530 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 906000 906200 :=
  FiniteIntervals.of_fin 906000 200 complete_chunk4530

lemma complete_chunk4531 : ∀ i : Fin 200, Compatible (906200 + i.val) →
    (table.lookup (906200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4531 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 906200 906400 :=
  FiniteIntervals.of_fin 906200 200 complete_chunk4531

lemma complete_chunk4532 : ∀ i : Fin 200, Compatible (906400 + i.val) →
    (table.lookup (906400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4532 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 906400 906600 :=
  FiniteIntervals.of_fin 906400 200 complete_chunk4532

lemma complete_chunk4533 : ∀ i : Fin 200, Compatible (906600 + i.val) →
    (table.lookup (906600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4533 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 906600 906800 :=
  FiniteIntervals.of_fin 906600 200 complete_chunk4533

lemma complete_chunk4534 : ∀ i : Fin 200, Compatible (906800 + i.val) →
    (table.lookup (906800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4534 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 906800 907000 :=
  FiniteIntervals.of_fin 906800 200 complete_chunk4534

lemma complete_chunk4535 : ∀ i : Fin 200, Compatible (907000 + i.val) →
    (table.lookup (907000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4535 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 907000 907200 :=
  FiniteIntervals.of_fin 907000 200 complete_chunk4535

lemma complete_chunk4536 : ∀ i : Fin 200, Compatible (907200 + i.val) →
    (table.lookup (907200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4536 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 907200 907400 :=
  FiniteIntervals.of_fin 907200 200 complete_chunk4536

lemma complete_chunk4537 : ∀ i : Fin 200, Compatible (907400 + i.val) →
    (table.lookup (907400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4537 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 907400 907600 :=
  FiniteIntervals.of_fin 907400 200 complete_chunk4537

lemma complete_chunk4538 : ∀ i : Fin 200, Compatible (907600 + i.val) →
    (table.lookup (907600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4538 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 907600 907800 :=
  FiniteIntervals.of_fin 907600 200 complete_chunk4538

lemma complete_chunk4539 : ∀ i : Fin 200, Compatible (907800 + i.val) →
    (table.lookup (907800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4539 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 907800 908000 :=
  FiniteIntervals.of_fin 907800 200 complete_chunk4539

#print axioms interval_chunk4530
end Erdos184Work.PureFiveFilter4
