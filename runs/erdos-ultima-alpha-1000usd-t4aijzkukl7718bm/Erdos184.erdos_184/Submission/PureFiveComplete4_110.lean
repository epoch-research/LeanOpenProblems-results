import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1100 : ∀ i : Fin 200, Compatible (220000 + i.val) →
    (table.lookup (220000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1100 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 220000 220200 :=
  FiniteIntervals.of_fin 220000 200 complete_chunk1100

lemma complete_chunk1101 : ∀ i : Fin 200, Compatible (220200 + i.val) →
    (table.lookup (220200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1101 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 220200 220400 :=
  FiniteIntervals.of_fin 220200 200 complete_chunk1101

lemma complete_chunk1102 : ∀ i : Fin 200, Compatible (220400 + i.val) →
    (table.lookup (220400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1102 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 220400 220600 :=
  FiniteIntervals.of_fin 220400 200 complete_chunk1102

lemma complete_chunk1103 : ∀ i : Fin 200, Compatible (220600 + i.val) →
    (table.lookup (220600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1103 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 220600 220800 :=
  FiniteIntervals.of_fin 220600 200 complete_chunk1103

lemma complete_chunk1104 : ∀ i : Fin 200, Compatible (220800 + i.val) →
    (table.lookup (220800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1104 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 220800 221000 :=
  FiniteIntervals.of_fin 220800 200 complete_chunk1104

lemma complete_chunk1105 : ∀ i : Fin 200, Compatible (221000 + i.val) →
    (table.lookup (221000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1105 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 221000 221200 :=
  FiniteIntervals.of_fin 221000 200 complete_chunk1105

lemma complete_chunk1106 : ∀ i : Fin 200, Compatible (221200 + i.val) →
    (table.lookup (221200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1106 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 221200 221400 :=
  FiniteIntervals.of_fin 221200 200 complete_chunk1106

lemma complete_chunk1107 : ∀ i : Fin 200, Compatible (221400 + i.val) →
    (table.lookup (221400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1107 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 221400 221600 :=
  FiniteIntervals.of_fin 221400 200 complete_chunk1107

lemma complete_chunk1108 : ∀ i : Fin 200, Compatible (221600 + i.val) →
    (table.lookup (221600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1108 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 221600 221800 :=
  FiniteIntervals.of_fin 221600 200 complete_chunk1108

lemma complete_chunk1109 : ∀ i : Fin 200, Compatible (221800 + i.val) →
    (table.lookup (221800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1109 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 221800 222000 :=
  FiniteIntervals.of_fin 221800 200 complete_chunk1109

#print axioms interval_chunk1100
end Erdos184Work.PureFiveFilter4
