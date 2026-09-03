import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6070 : ∀ i : Fin 200, Compatible (1214000 + i.val) →
    (table.lookup (1214000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6070 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1214000 1214200 :=
  FiniteIntervals.of_fin 1214000 200 complete_chunk6070

lemma complete_chunk6071 : ∀ i : Fin 200, Compatible (1214200 + i.val) →
    (table.lookup (1214200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6071 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1214200 1214400 :=
  FiniteIntervals.of_fin 1214200 200 complete_chunk6071

lemma complete_chunk6072 : ∀ i : Fin 200, Compatible (1214400 + i.val) →
    (table.lookup (1214400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6072 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1214400 1214600 :=
  FiniteIntervals.of_fin 1214400 200 complete_chunk6072

lemma complete_chunk6073 : ∀ i : Fin 200, Compatible (1214600 + i.val) →
    (table.lookup (1214600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6073 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1214600 1214800 :=
  FiniteIntervals.of_fin 1214600 200 complete_chunk6073

lemma complete_chunk6074 : ∀ i : Fin 200, Compatible (1214800 + i.val) →
    (table.lookup (1214800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6074 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1214800 1215000 :=
  FiniteIntervals.of_fin 1214800 200 complete_chunk6074

lemma complete_chunk6075 : ∀ i : Fin 200, Compatible (1215000 + i.val) →
    (table.lookup (1215000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6075 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1215000 1215200 :=
  FiniteIntervals.of_fin 1215000 200 complete_chunk6075

lemma complete_chunk6076 : ∀ i : Fin 200, Compatible (1215200 + i.val) →
    (table.lookup (1215200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6076 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1215200 1215400 :=
  FiniteIntervals.of_fin 1215200 200 complete_chunk6076

lemma complete_chunk6077 : ∀ i : Fin 200, Compatible (1215400 + i.val) →
    (table.lookup (1215400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6077 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1215400 1215600 :=
  FiniteIntervals.of_fin 1215400 200 complete_chunk6077

lemma complete_chunk6078 : ∀ i : Fin 200, Compatible (1215600 + i.val) →
    (table.lookup (1215600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6078 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1215600 1215800 :=
  FiniteIntervals.of_fin 1215600 200 complete_chunk6078

lemma complete_chunk6079 : ∀ i : Fin 200, Compatible (1215800 + i.val) →
    (table.lookup (1215800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6079 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1215800 1216000 :=
  FiniteIntervals.of_fin 1215800 200 complete_chunk6079

#print axioms interval_chunk6070
end Erdos184Work.PureFiveFilter4
