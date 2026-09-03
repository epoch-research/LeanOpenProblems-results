import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5020 : ∀ i : Fin 200, Compatible (1004000 + i.val) →
    (table.lookup (1004000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5020 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1004000 1004200 :=
  FiniteIntervals.of_fin 1004000 200 complete_chunk5020

lemma complete_chunk5021 : ∀ i : Fin 200, Compatible (1004200 + i.val) →
    (table.lookup (1004200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5021 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1004200 1004400 :=
  FiniteIntervals.of_fin 1004200 200 complete_chunk5021

lemma complete_chunk5022 : ∀ i : Fin 200, Compatible (1004400 + i.val) →
    (table.lookup (1004400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5022 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1004400 1004600 :=
  FiniteIntervals.of_fin 1004400 200 complete_chunk5022

lemma complete_chunk5023 : ∀ i : Fin 200, Compatible (1004600 + i.val) →
    (table.lookup (1004600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5023 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1004600 1004800 :=
  FiniteIntervals.of_fin 1004600 200 complete_chunk5023

lemma complete_chunk5024 : ∀ i : Fin 200, Compatible (1004800 + i.val) →
    (table.lookup (1004800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5024 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1004800 1005000 :=
  FiniteIntervals.of_fin 1004800 200 complete_chunk5024

lemma complete_chunk5025 : ∀ i : Fin 200, Compatible (1005000 + i.val) →
    (table.lookup (1005000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5025 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1005000 1005200 :=
  FiniteIntervals.of_fin 1005000 200 complete_chunk5025

lemma complete_chunk5026 : ∀ i : Fin 200, Compatible (1005200 + i.val) →
    (table.lookup (1005200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5026 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1005200 1005400 :=
  FiniteIntervals.of_fin 1005200 200 complete_chunk5026

lemma complete_chunk5027 : ∀ i : Fin 200, Compatible (1005400 + i.val) →
    (table.lookup (1005400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5027 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1005400 1005600 :=
  FiniteIntervals.of_fin 1005400 200 complete_chunk5027

lemma complete_chunk5028 : ∀ i : Fin 200, Compatible (1005600 + i.val) →
    (table.lookup (1005600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5028 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1005600 1005800 :=
  FiniteIntervals.of_fin 1005600 200 complete_chunk5028

lemma complete_chunk5029 : ∀ i : Fin 200, Compatible (1005800 + i.val) →
    (table.lookup (1005800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5029 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1005800 1006000 :=
  FiniteIntervals.of_fin 1005800 200 complete_chunk5029

#print axioms interval_chunk5020
end Erdos184Work.PureFiveFilter4
