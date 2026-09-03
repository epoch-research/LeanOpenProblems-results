import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1020 : ∀ i : Fin 200, Compatible (204000 + i.val) →
    (table.lookup (204000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1020 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 204000 204200 :=
  FiniteIntervals.of_fin 204000 200 complete_chunk1020

lemma complete_chunk1021 : ∀ i : Fin 200, Compatible (204200 + i.val) →
    (table.lookup (204200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1021 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 204200 204400 :=
  FiniteIntervals.of_fin 204200 200 complete_chunk1021

lemma complete_chunk1022 : ∀ i : Fin 200, Compatible (204400 + i.val) →
    (table.lookup (204400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1022 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 204400 204600 :=
  FiniteIntervals.of_fin 204400 200 complete_chunk1022

lemma complete_chunk1023 : ∀ i : Fin 200, Compatible (204600 + i.val) →
    (table.lookup (204600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1023 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 204600 204800 :=
  FiniteIntervals.of_fin 204600 200 complete_chunk1023

lemma complete_chunk1024 : ∀ i : Fin 200, Compatible (204800 + i.val) →
    (table.lookup (204800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1024 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 204800 205000 :=
  FiniteIntervals.of_fin 204800 200 complete_chunk1024

lemma complete_chunk1025 : ∀ i : Fin 200, Compatible (205000 + i.val) →
    (table.lookup (205000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1025 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 205000 205200 :=
  FiniteIntervals.of_fin 205000 200 complete_chunk1025

lemma complete_chunk1026 : ∀ i : Fin 200, Compatible (205200 + i.val) →
    (table.lookup (205200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1026 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 205200 205400 :=
  FiniteIntervals.of_fin 205200 200 complete_chunk1026

lemma complete_chunk1027 : ∀ i : Fin 200, Compatible (205400 + i.val) →
    (table.lookup (205400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1027 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 205400 205600 :=
  FiniteIntervals.of_fin 205400 200 complete_chunk1027

lemma complete_chunk1028 : ∀ i : Fin 200, Compatible (205600 + i.val) →
    (table.lookup (205600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1028 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 205600 205800 :=
  FiniteIntervals.of_fin 205600 200 complete_chunk1028

lemma complete_chunk1029 : ∀ i : Fin 200, Compatible (205800 + i.val) →
    (table.lookup (205800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1029 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 205800 206000 :=
  FiniteIntervals.of_fin 205800 200 complete_chunk1029

#print axioms interval_chunk1020
end Erdos184Work.PureFiveFilter4
