import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3600 : ∀ i : Fin 200, Compatible (720000 + i.val) →
    (table.lookup (720000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3600 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 720000 720200 :=
  FiniteIntervals.of_fin 720000 200 complete_chunk3600

lemma complete_chunk3601 : ∀ i : Fin 200, Compatible (720200 + i.val) →
    (table.lookup (720200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3601 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 720200 720400 :=
  FiniteIntervals.of_fin 720200 200 complete_chunk3601

lemma complete_chunk3602 : ∀ i : Fin 200, Compatible (720400 + i.val) →
    (table.lookup (720400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3602 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 720400 720600 :=
  FiniteIntervals.of_fin 720400 200 complete_chunk3602

lemma complete_chunk3603 : ∀ i : Fin 200, Compatible (720600 + i.val) →
    (table.lookup (720600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3603 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 720600 720800 :=
  FiniteIntervals.of_fin 720600 200 complete_chunk3603

lemma complete_chunk3604 : ∀ i : Fin 200, Compatible (720800 + i.val) →
    (table.lookup (720800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3604 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 720800 721000 :=
  FiniteIntervals.of_fin 720800 200 complete_chunk3604

lemma complete_chunk3605 : ∀ i : Fin 200, Compatible (721000 + i.val) →
    (table.lookup (721000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3605 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 721000 721200 :=
  FiniteIntervals.of_fin 721000 200 complete_chunk3605

lemma complete_chunk3606 : ∀ i : Fin 200, Compatible (721200 + i.val) →
    (table.lookup (721200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3606 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 721200 721400 :=
  FiniteIntervals.of_fin 721200 200 complete_chunk3606

lemma complete_chunk3607 : ∀ i : Fin 200, Compatible (721400 + i.val) →
    (table.lookup (721400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3607 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 721400 721600 :=
  FiniteIntervals.of_fin 721400 200 complete_chunk3607

lemma complete_chunk3608 : ∀ i : Fin 200, Compatible (721600 + i.val) →
    (table.lookup (721600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3608 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 721600 721800 :=
  FiniteIntervals.of_fin 721600 200 complete_chunk3608

lemma complete_chunk3609 : ∀ i : Fin 200, Compatible (721800 + i.val) →
    (table.lookup (721800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3609 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 721800 722000 :=
  FiniteIntervals.of_fin 721800 200 complete_chunk3609

#print axioms interval_chunk3600
end Erdos184Work.PureFiveFilter4
