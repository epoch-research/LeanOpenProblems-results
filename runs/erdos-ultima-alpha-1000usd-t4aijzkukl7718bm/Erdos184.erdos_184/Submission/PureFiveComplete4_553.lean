import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5530 : ∀ i : Fin 200, Compatible (1106000 + i.val) →
    (table.lookup (1106000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5530 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1106000 1106200 :=
  FiniteIntervals.of_fin 1106000 200 complete_chunk5530

lemma complete_chunk5531 : ∀ i : Fin 200, Compatible (1106200 + i.val) →
    (table.lookup (1106200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5531 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1106200 1106400 :=
  FiniteIntervals.of_fin 1106200 200 complete_chunk5531

lemma complete_chunk5532 : ∀ i : Fin 200, Compatible (1106400 + i.val) →
    (table.lookup (1106400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5532 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1106400 1106600 :=
  FiniteIntervals.of_fin 1106400 200 complete_chunk5532

lemma complete_chunk5533 : ∀ i : Fin 200, Compatible (1106600 + i.val) →
    (table.lookup (1106600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5533 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1106600 1106800 :=
  FiniteIntervals.of_fin 1106600 200 complete_chunk5533

lemma complete_chunk5534 : ∀ i : Fin 200, Compatible (1106800 + i.val) →
    (table.lookup (1106800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5534 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1106800 1107000 :=
  FiniteIntervals.of_fin 1106800 200 complete_chunk5534

lemma complete_chunk5535 : ∀ i : Fin 200, Compatible (1107000 + i.val) →
    (table.lookup (1107000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5535 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1107000 1107200 :=
  FiniteIntervals.of_fin 1107000 200 complete_chunk5535

lemma complete_chunk5536 : ∀ i : Fin 200, Compatible (1107200 + i.val) →
    (table.lookup (1107200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5536 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1107200 1107400 :=
  FiniteIntervals.of_fin 1107200 200 complete_chunk5536

lemma complete_chunk5537 : ∀ i : Fin 200, Compatible (1107400 + i.val) →
    (table.lookup (1107400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5537 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1107400 1107600 :=
  FiniteIntervals.of_fin 1107400 200 complete_chunk5537

lemma complete_chunk5538 : ∀ i : Fin 200, Compatible (1107600 + i.val) →
    (table.lookup (1107600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5538 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1107600 1107800 :=
  FiniteIntervals.of_fin 1107600 200 complete_chunk5538

lemma complete_chunk5539 : ∀ i : Fin 200, Compatible (1107800 + i.val) →
    (table.lookup (1107800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5539 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1107800 1108000 :=
  FiniteIntervals.of_fin 1107800 200 complete_chunk5539

#print axioms interval_chunk5530
end Erdos184Work.PureFiveFilter4
