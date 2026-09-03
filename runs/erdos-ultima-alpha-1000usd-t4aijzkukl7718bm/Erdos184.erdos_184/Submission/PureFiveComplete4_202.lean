import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2020 : ∀ i : Fin 200, Compatible (404000 + i.val) →
    (table.lookup (404000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2020 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 404000 404200 :=
  FiniteIntervals.of_fin 404000 200 complete_chunk2020

lemma complete_chunk2021 : ∀ i : Fin 200, Compatible (404200 + i.val) →
    (table.lookup (404200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2021 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 404200 404400 :=
  FiniteIntervals.of_fin 404200 200 complete_chunk2021

lemma complete_chunk2022 : ∀ i : Fin 200, Compatible (404400 + i.val) →
    (table.lookup (404400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2022 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 404400 404600 :=
  FiniteIntervals.of_fin 404400 200 complete_chunk2022

lemma complete_chunk2023 : ∀ i : Fin 200, Compatible (404600 + i.val) →
    (table.lookup (404600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2023 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 404600 404800 :=
  FiniteIntervals.of_fin 404600 200 complete_chunk2023

lemma complete_chunk2024 : ∀ i : Fin 200, Compatible (404800 + i.val) →
    (table.lookup (404800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2024 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 404800 405000 :=
  FiniteIntervals.of_fin 404800 200 complete_chunk2024

lemma complete_chunk2025 : ∀ i : Fin 200, Compatible (405000 + i.val) →
    (table.lookup (405000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2025 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 405000 405200 :=
  FiniteIntervals.of_fin 405000 200 complete_chunk2025

lemma complete_chunk2026 : ∀ i : Fin 200, Compatible (405200 + i.val) →
    (table.lookup (405200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2026 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 405200 405400 :=
  FiniteIntervals.of_fin 405200 200 complete_chunk2026

lemma complete_chunk2027 : ∀ i : Fin 200, Compatible (405400 + i.val) →
    (table.lookup (405400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2027 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 405400 405600 :=
  FiniteIntervals.of_fin 405400 200 complete_chunk2027

lemma complete_chunk2028 : ∀ i : Fin 200, Compatible (405600 + i.val) →
    (table.lookup (405600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2028 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 405600 405800 :=
  FiniteIntervals.of_fin 405600 200 complete_chunk2028

lemma complete_chunk2029 : ∀ i : Fin 200, Compatible (405800 + i.val) →
    (table.lookup (405800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2029 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 405800 406000 :=
  FiniteIntervals.of_fin 405800 200 complete_chunk2029

#print axioms interval_chunk2020
end Erdos184Work.PureFiveFilter4
