import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2600 : ∀ i : Fin 200, Compatible (520000 + i.val) →
    (table.lookup (520000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2600 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 520000 520200 :=
  FiniteIntervals.of_fin 520000 200 complete_chunk2600

lemma complete_chunk2601 : ∀ i : Fin 200, Compatible (520200 + i.val) →
    (table.lookup (520200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2601 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 520200 520400 :=
  FiniteIntervals.of_fin 520200 200 complete_chunk2601

lemma complete_chunk2602 : ∀ i : Fin 200, Compatible (520400 + i.val) →
    (table.lookup (520400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2602 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 520400 520600 :=
  FiniteIntervals.of_fin 520400 200 complete_chunk2602

lemma complete_chunk2603 : ∀ i : Fin 200, Compatible (520600 + i.val) →
    (table.lookup (520600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2603 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 520600 520800 :=
  FiniteIntervals.of_fin 520600 200 complete_chunk2603

lemma complete_chunk2604 : ∀ i : Fin 200, Compatible (520800 + i.val) →
    (table.lookup (520800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2604 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 520800 521000 :=
  FiniteIntervals.of_fin 520800 200 complete_chunk2604

lemma complete_chunk2605 : ∀ i : Fin 200, Compatible (521000 + i.val) →
    (table.lookup (521000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2605 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 521000 521200 :=
  FiniteIntervals.of_fin 521000 200 complete_chunk2605

lemma complete_chunk2606 : ∀ i : Fin 200, Compatible (521200 + i.val) →
    (table.lookup (521200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2606 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 521200 521400 :=
  FiniteIntervals.of_fin 521200 200 complete_chunk2606

lemma complete_chunk2607 : ∀ i : Fin 200, Compatible (521400 + i.val) →
    (table.lookup (521400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2607 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 521400 521600 :=
  FiniteIntervals.of_fin 521400 200 complete_chunk2607

lemma complete_chunk2608 : ∀ i : Fin 200, Compatible (521600 + i.val) →
    (table.lookup (521600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2608 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 521600 521800 :=
  FiniteIntervals.of_fin 521600 200 complete_chunk2608

lemma complete_chunk2609 : ∀ i : Fin 200, Compatible (521800 + i.val) →
    (table.lookup (521800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2609 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 521800 522000 :=
  FiniteIntervals.of_fin 521800 200 complete_chunk2609

#print axioms interval_chunk2600
end Erdos184Work.PureFiveFilter4
