import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3020 : ∀ i : Fin 200, Compatible (604000 + i.val) →
    (table.lookup (604000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3020 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 604000 604200 :=
  FiniteIntervals.of_fin 604000 200 complete_chunk3020

lemma complete_chunk3021 : ∀ i : Fin 200, Compatible (604200 + i.val) →
    (table.lookup (604200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3021 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 604200 604400 :=
  FiniteIntervals.of_fin 604200 200 complete_chunk3021

lemma complete_chunk3022 : ∀ i : Fin 200, Compatible (604400 + i.val) →
    (table.lookup (604400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3022 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 604400 604600 :=
  FiniteIntervals.of_fin 604400 200 complete_chunk3022

lemma complete_chunk3023 : ∀ i : Fin 200, Compatible (604600 + i.val) →
    (table.lookup (604600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3023 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 604600 604800 :=
  FiniteIntervals.of_fin 604600 200 complete_chunk3023

lemma complete_chunk3024 : ∀ i : Fin 200, Compatible (604800 + i.val) →
    (table.lookup (604800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3024 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 604800 605000 :=
  FiniteIntervals.of_fin 604800 200 complete_chunk3024

lemma complete_chunk3025 : ∀ i : Fin 200, Compatible (605000 + i.val) →
    (table.lookup (605000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3025 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 605000 605200 :=
  FiniteIntervals.of_fin 605000 200 complete_chunk3025

lemma complete_chunk3026 : ∀ i : Fin 200, Compatible (605200 + i.val) →
    (table.lookup (605200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3026 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 605200 605400 :=
  FiniteIntervals.of_fin 605200 200 complete_chunk3026

lemma complete_chunk3027 : ∀ i : Fin 200, Compatible (605400 + i.val) →
    (table.lookup (605400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3027 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 605400 605600 :=
  FiniteIntervals.of_fin 605400 200 complete_chunk3027

lemma complete_chunk3028 : ∀ i : Fin 200, Compatible (605600 + i.val) →
    (table.lookup (605600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3028 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 605600 605800 :=
  FiniteIntervals.of_fin 605600 200 complete_chunk3028

lemma complete_chunk3029 : ∀ i : Fin 200, Compatible (605800 + i.val) →
    (table.lookup (605800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3029 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 605800 606000 :=
  FiniteIntervals.of_fin 605800 200 complete_chunk3029

#print axioms interval_chunk3020
end Erdos184Work.PureFiveFilter4
