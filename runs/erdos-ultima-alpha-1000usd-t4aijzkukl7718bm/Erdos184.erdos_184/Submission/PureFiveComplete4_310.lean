import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3100 : ∀ i : Fin 200, Compatible (620000 + i.val) →
    (table.lookup (620000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3100 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 620000 620200 :=
  FiniteIntervals.of_fin 620000 200 complete_chunk3100

lemma complete_chunk3101 : ∀ i : Fin 200, Compatible (620200 + i.val) →
    (table.lookup (620200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3101 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 620200 620400 :=
  FiniteIntervals.of_fin 620200 200 complete_chunk3101

lemma complete_chunk3102 : ∀ i : Fin 200, Compatible (620400 + i.val) →
    (table.lookup (620400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3102 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 620400 620600 :=
  FiniteIntervals.of_fin 620400 200 complete_chunk3102

lemma complete_chunk3103 : ∀ i : Fin 200, Compatible (620600 + i.val) →
    (table.lookup (620600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3103 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 620600 620800 :=
  FiniteIntervals.of_fin 620600 200 complete_chunk3103

lemma complete_chunk3104 : ∀ i : Fin 200, Compatible (620800 + i.val) →
    (table.lookup (620800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3104 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 620800 621000 :=
  FiniteIntervals.of_fin 620800 200 complete_chunk3104

lemma complete_chunk3105 : ∀ i : Fin 200, Compatible (621000 + i.val) →
    (table.lookup (621000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3105 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 621000 621200 :=
  FiniteIntervals.of_fin 621000 200 complete_chunk3105

lemma complete_chunk3106 : ∀ i : Fin 200, Compatible (621200 + i.val) →
    (table.lookup (621200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3106 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 621200 621400 :=
  FiniteIntervals.of_fin 621200 200 complete_chunk3106

lemma complete_chunk3107 : ∀ i : Fin 200, Compatible (621400 + i.val) →
    (table.lookup (621400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3107 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 621400 621600 :=
  FiniteIntervals.of_fin 621400 200 complete_chunk3107

lemma complete_chunk3108 : ∀ i : Fin 200, Compatible (621600 + i.val) →
    (table.lookup (621600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3108 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 621600 621800 :=
  FiniteIntervals.of_fin 621600 200 complete_chunk3108

lemma complete_chunk3109 : ∀ i : Fin 200, Compatible (621800 + i.val) →
    (table.lookup (621800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3109 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 621800 622000 :=
  FiniteIntervals.of_fin 621800 200 complete_chunk3109

#print axioms interval_chunk3100
end Erdos184Work.PureFiveFilter4
