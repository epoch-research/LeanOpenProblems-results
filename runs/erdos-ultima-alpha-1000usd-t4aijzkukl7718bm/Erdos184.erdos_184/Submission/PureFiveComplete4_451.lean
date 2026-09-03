import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4510 : ∀ i : Fin 200, Compatible (902000 + i.val) →
    (table.lookup (902000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4510 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 902000 902200 :=
  FiniteIntervals.of_fin 902000 200 complete_chunk4510

lemma complete_chunk4511 : ∀ i : Fin 200, Compatible (902200 + i.val) →
    (table.lookup (902200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4511 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 902200 902400 :=
  FiniteIntervals.of_fin 902200 200 complete_chunk4511

lemma complete_chunk4512 : ∀ i : Fin 200, Compatible (902400 + i.val) →
    (table.lookup (902400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4512 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 902400 902600 :=
  FiniteIntervals.of_fin 902400 200 complete_chunk4512

lemma complete_chunk4513 : ∀ i : Fin 200, Compatible (902600 + i.val) →
    (table.lookup (902600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4513 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 902600 902800 :=
  FiniteIntervals.of_fin 902600 200 complete_chunk4513

lemma complete_chunk4514 : ∀ i : Fin 200, Compatible (902800 + i.val) →
    (table.lookup (902800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4514 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 902800 903000 :=
  FiniteIntervals.of_fin 902800 200 complete_chunk4514

lemma complete_chunk4515 : ∀ i : Fin 200, Compatible (903000 + i.val) →
    (table.lookup (903000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4515 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 903000 903200 :=
  FiniteIntervals.of_fin 903000 200 complete_chunk4515

lemma complete_chunk4516 : ∀ i : Fin 200, Compatible (903200 + i.val) →
    (table.lookup (903200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4516 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 903200 903400 :=
  FiniteIntervals.of_fin 903200 200 complete_chunk4516

lemma complete_chunk4517 : ∀ i : Fin 200, Compatible (903400 + i.val) →
    (table.lookup (903400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4517 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 903400 903600 :=
  FiniteIntervals.of_fin 903400 200 complete_chunk4517

lemma complete_chunk4518 : ∀ i : Fin 200, Compatible (903600 + i.val) →
    (table.lookup (903600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4518 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 903600 903800 :=
  FiniteIntervals.of_fin 903600 200 complete_chunk4518

lemma complete_chunk4519 : ∀ i : Fin 200, Compatible (903800 + i.val) →
    (table.lookup (903800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4519 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 903800 904000 :=
  FiniteIntervals.of_fin 903800 200 complete_chunk4519

#print axioms interval_chunk4510
end Erdos184Work.PureFiveFilter4
