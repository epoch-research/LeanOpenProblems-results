import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6020 : ∀ i : Fin 200, Compatible (1204000 + i.val) →
    (table.lookup (1204000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6020 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1204000 1204200 :=
  FiniteIntervals.of_fin 1204000 200 complete_chunk6020

lemma complete_chunk6021 : ∀ i : Fin 200, Compatible (1204200 + i.val) →
    (table.lookup (1204200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6021 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1204200 1204400 :=
  FiniteIntervals.of_fin 1204200 200 complete_chunk6021

lemma complete_chunk6022 : ∀ i : Fin 200, Compatible (1204400 + i.val) →
    (table.lookup (1204400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6022 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1204400 1204600 :=
  FiniteIntervals.of_fin 1204400 200 complete_chunk6022

lemma complete_chunk6023 : ∀ i : Fin 200, Compatible (1204600 + i.val) →
    (table.lookup (1204600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6023 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1204600 1204800 :=
  FiniteIntervals.of_fin 1204600 200 complete_chunk6023

lemma complete_chunk6024 : ∀ i : Fin 200, Compatible (1204800 + i.val) →
    (table.lookup (1204800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6024 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1204800 1205000 :=
  FiniteIntervals.of_fin 1204800 200 complete_chunk6024

lemma complete_chunk6025 : ∀ i : Fin 200, Compatible (1205000 + i.val) →
    (table.lookup (1205000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6025 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1205000 1205200 :=
  FiniteIntervals.of_fin 1205000 200 complete_chunk6025

lemma complete_chunk6026 : ∀ i : Fin 200, Compatible (1205200 + i.val) →
    (table.lookup (1205200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6026 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1205200 1205400 :=
  FiniteIntervals.of_fin 1205200 200 complete_chunk6026

lemma complete_chunk6027 : ∀ i : Fin 200, Compatible (1205400 + i.val) →
    (table.lookup (1205400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6027 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1205400 1205600 :=
  FiniteIntervals.of_fin 1205400 200 complete_chunk6027

lemma complete_chunk6028 : ∀ i : Fin 200, Compatible (1205600 + i.val) →
    (table.lookup (1205600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6028 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1205600 1205800 :=
  FiniteIntervals.of_fin 1205600 200 complete_chunk6028

lemma complete_chunk6029 : ∀ i : Fin 200, Compatible (1205800 + i.val) →
    (table.lookup (1205800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6029 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1205800 1206000 :=
  FiniteIntervals.of_fin 1205800 200 complete_chunk6029

#print axioms interval_chunk6020
end Erdos184Work.PureFiveFilter4
