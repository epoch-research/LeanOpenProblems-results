import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4020 : ∀ i : Fin 200, Compatible (804000 + i.val) →
    (table.lookup (804000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4020 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 804000 804200 :=
  FiniteIntervals.of_fin 804000 200 complete_chunk4020

lemma complete_chunk4021 : ∀ i : Fin 200, Compatible (804200 + i.val) →
    (table.lookup (804200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4021 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 804200 804400 :=
  FiniteIntervals.of_fin 804200 200 complete_chunk4021

lemma complete_chunk4022 : ∀ i : Fin 200, Compatible (804400 + i.val) →
    (table.lookup (804400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4022 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 804400 804600 :=
  FiniteIntervals.of_fin 804400 200 complete_chunk4022

lemma complete_chunk4023 : ∀ i : Fin 200, Compatible (804600 + i.val) →
    (table.lookup (804600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4023 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 804600 804800 :=
  FiniteIntervals.of_fin 804600 200 complete_chunk4023

lemma complete_chunk4024 : ∀ i : Fin 200, Compatible (804800 + i.val) →
    (table.lookup (804800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4024 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 804800 805000 :=
  FiniteIntervals.of_fin 804800 200 complete_chunk4024

lemma complete_chunk4025 : ∀ i : Fin 200, Compatible (805000 + i.val) →
    (table.lookup (805000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4025 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 805000 805200 :=
  FiniteIntervals.of_fin 805000 200 complete_chunk4025

lemma complete_chunk4026 : ∀ i : Fin 200, Compatible (805200 + i.val) →
    (table.lookup (805200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4026 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 805200 805400 :=
  FiniteIntervals.of_fin 805200 200 complete_chunk4026

lemma complete_chunk4027 : ∀ i : Fin 200, Compatible (805400 + i.val) →
    (table.lookup (805400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4027 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 805400 805600 :=
  FiniteIntervals.of_fin 805400 200 complete_chunk4027

lemma complete_chunk4028 : ∀ i : Fin 200, Compatible (805600 + i.val) →
    (table.lookup (805600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4028 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 805600 805800 :=
  FiniteIntervals.of_fin 805600 200 complete_chunk4028

lemma complete_chunk4029 : ∀ i : Fin 200, Compatible (805800 + i.val) →
    (table.lookup (805800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4029 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 805800 806000 :=
  FiniteIntervals.of_fin 805800 200 complete_chunk4029

#print axioms interval_chunk4020
end Erdos184Work.PureFiveFilter4
