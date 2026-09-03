import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1070 : ∀ i : Fin 200, Compatible (214000 + i.val) →
    (table.lookup (214000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1070 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 214000 214200 :=
  FiniteIntervals.of_fin 214000 200 complete_chunk1070

lemma complete_chunk1071 : ∀ i : Fin 200, Compatible (214200 + i.val) →
    (table.lookup (214200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1071 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 214200 214400 :=
  FiniteIntervals.of_fin 214200 200 complete_chunk1071

lemma complete_chunk1072 : ∀ i : Fin 200, Compatible (214400 + i.val) →
    (table.lookup (214400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1072 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 214400 214600 :=
  FiniteIntervals.of_fin 214400 200 complete_chunk1072

lemma complete_chunk1073 : ∀ i : Fin 200, Compatible (214600 + i.val) →
    (table.lookup (214600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1073 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 214600 214800 :=
  FiniteIntervals.of_fin 214600 200 complete_chunk1073

lemma complete_chunk1074 : ∀ i : Fin 200, Compatible (214800 + i.val) →
    (table.lookup (214800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1074 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 214800 215000 :=
  FiniteIntervals.of_fin 214800 200 complete_chunk1074

lemma complete_chunk1075 : ∀ i : Fin 200, Compatible (215000 + i.val) →
    (table.lookup (215000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1075 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 215000 215200 :=
  FiniteIntervals.of_fin 215000 200 complete_chunk1075

lemma complete_chunk1076 : ∀ i : Fin 200, Compatible (215200 + i.val) →
    (table.lookup (215200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1076 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 215200 215400 :=
  FiniteIntervals.of_fin 215200 200 complete_chunk1076

lemma complete_chunk1077 : ∀ i : Fin 200, Compatible (215400 + i.val) →
    (table.lookup (215400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1077 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 215400 215600 :=
  FiniteIntervals.of_fin 215400 200 complete_chunk1077

lemma complete_chunk1078 : ∀ i : Fin 200, Compatible (215600 + i.val) →
    (table.lookup (215600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1078 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 215600 215800 :=
  FiniteIntervals.of_fin 215600 200 complete_chunk1078

lemma complete_chunk1079 : ∀ i : Fin 200, Compatible (215800 + i.val) →
    (table.lookup (215800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1079 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 215800 216000 :=
  FiniteIntervals.of_fin 215800 200 complete_chunk1079

#print axioms interval_chunk1070
end Erdos184Work.PureFiveFilter4
