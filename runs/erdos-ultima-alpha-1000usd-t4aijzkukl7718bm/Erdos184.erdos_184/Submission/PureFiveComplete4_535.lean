import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5350 : ∀ i : Fin 200, Compatible (1070000 + i.val) →
    (table.lookup (1070000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5350 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1070000 1070200 :=
  FiniteIntervals.of_fin 1070000 200 complete_chunk5350

lemma complete_chunk5351 : ∀ i : Fin 200, Compatible (1070200 + i.val) →
    (table.lookup (1070200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5351 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1070200 1070400 :=
  FiniteIntervals.of_fin 1070200 200 complete_chunk5351

lemma complete_chunk5352 : ∀ i : Fin 200, Compatible (1070400 + i.val) →
    (table.lookup (1070400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5352 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1070400 1070600 :=
  FiniteIntervals.of_fin 1070400 200 complete_chunk5352

lemma complete_chunk5353 : ∀ i : Fin 200, Compatible (1070600 + i.val) →
    (table.lookup (1070600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5353 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1070600 1070800 :=
  FiniteIntervals.of_fin 1070600 200 complete_chunk5353

lemma complete_chunk5354 : ∀ i : Fin 200, Compatible (1070800 + i.val) →
    (table.lookup (1070800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5354 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1070800 1071000 :=
  FiniteIntervals.of_fin 1070800 200 complete_chunk5354

lemma complete_chunk5355 : ∀ i : Fin 200, Compatible (1071000 + i.val) →
    (table.lookup (1071000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5355 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1071000 1071200 :=
  FiniteIntervals.of_fin 1071000 200 complete_chunk5355

lemma complete_chunk5356 : ∀ i : Fin 200, Compatible (1071200 + i.val) →
    (table.lookup (1071200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5356 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1071200 1071400 :=
  FiniteIntervals.of_fin 1071200 200 complete_chunk5356

lemma complete_chunk5357 : ∀ i : Fin 200, Compatible (1071400 + i.val) →
    (table.lookup (1071400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5357 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1071400 1071600 :=
  FiniteIntervals.of_fin 1071400 200 complete_chunk5357

lemma complete_chunk5358 : ∀ i : Fin 200, Compatible (1071600 + i.val) →
    (table.lookup (1071600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5358 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1071600 1071800 :=
  FiniteIntervals.of_fin 1071600 200 complete_chunk5358

lemma complete_chunk5359 : ∀ i : Fin 200, Compatible (1071800 + i.val) →
    (table.lookup (1071800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5359 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1071800 1072000 :=
  FiniteIntervals.of_fin 1071800 200 complete_chunk5359

#print axioms interval_chunk5350
end Erdos184Work.PureFiveFilter4
