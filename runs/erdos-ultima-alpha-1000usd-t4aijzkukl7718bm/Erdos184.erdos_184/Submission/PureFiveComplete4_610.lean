import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6100 : ∀ i : Fin 200, Compatible (1220000 + i.val) →
    (table.lookup (1220000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6100 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1220000 1220200 :=
  FiniteIntervals.of_fin 1220000 200 complete_chunk6100

lemma complete_chunk6101 : ∀ i : Fin 200, Compatible (1220200 + i.val) →
    (table.lookup (1220200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6101 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1220200 1220400 :=
  FiniteIntervals.of_fin 1220200 200 complete_chunk6101

lemma complete_chunk6102 : ∀ i : Fin 200, Compatible (1220400 + i.val) →
    (table.lookup (1220400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6102 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1220400 1220600 :=
  FiniteIntervals.of_fin 1220400 200 complete_chunk6102

lemma complete_chunk6103 : ∀ i : Fin 200, Compatible (1220600 + i.val) →
    (table.lookup (1220600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6103 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1220600 1220800 :=
  FiniteIntervals.of_fin 1220600 200 complete_chunk6103

lemma complete_chunk6104 : ∀ i : Fin 200, Compatible (1220800 + i.val) →
    (table.lookup (1220800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6104 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1220800 1221000 :=
  FiniteIntervals.of_fin 1220800 200 complete_chunk6104

lemma complete_chunk6105 : ∀ i : Fin 200, Compatible (1221000 + i.val) →
    (table.lookup (1221000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6105 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1221000 1221200 :=
  FiniteIntervals.of_fin 1221000 200 complete_chunk6105

lemma complete_chunk6106 : ∀ i : Fin 200, Compatible (1221200 + i.val) →
    (table.lookup (1221200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6106 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1221200 1221400 :=
  FiniteIntervals.of_fin 1221200 200 complete_chunk6106

lemma complete_chunk6107 : ∀ i : Fin 200, Compatible (1221400 + i.val) →
    (table.lookup (1221400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6107 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1221400 1221600 :=
  FiniteIntervals.of_fin 1221400 200 complete_chunk6107

lemma complete_chunk6108 : ∀ i : Fin 200, Compatible (1221600 + i.val) →
    (table.lookup (1221600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6108 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1221600 1221800 :=
  FiniteIntervals.of_fin 1221600 200 complete_chunk6108

lemma complete_chunk6109 : ∀ i : Fin 200, Compatible (1221800 + i.val) →
    (table.lookup (1221800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6109 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1221800 1222000 :=
  FiniteIntervals.of_fin 1221800 200 complete_chunk6109

#print axioms interval_chunk6100
end Erdos184Work.PureFiveFilter4
