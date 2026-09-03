import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6130 : ∀ i : Fin 200, Compatible (1226000 + i.val) →
    (table.lookup (1226000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6130 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1226000 1226200 :=
  FiniteIntervals.of_fin 1226000 200 complete_chunk6130

lemma complete_chunk6131 : ∀ i : Fin 200, Compatible (1226200 + i.val) →
    (table.lookup (1226200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6131 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1226200 1226400 :=
  FiniteIntervals.of_fin 1226200 200 complete_chunk6131

lemma complete_chunk6132 : ∀ i : Fin 200, Compatible (1226400 + i.val) →
    (table.lookup (1226400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6132 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1226400 1226600 :=
  FiniteIntervals.of_fin 1226400 200 complete_chunk6132

lemma complete_chunk6133 : ∀ i : Fin 200, Compatible (1226600 + i.val) →
    (table.lookup (1226600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6133 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1226600 1226800 :=
  FiniteIntervals.of_fin 1226600 200 complete_chunk6133

lemma complete_chunk6134 : ∀ i : Fin 200, Compatible (1226800 + i.val) →
    (table.lookup (1226800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6134 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1226800 1227000 :=
  FiniteIntervals.of_fin 1226800 200 complete_chunk6134

lemma complete_chunk6135 : ∀ i : Fin 200, Compatible (1227000 + i.val) →
    (table.lookup (1227000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6135 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1227000 1227200 :=
  FiniteIntervals.of_fin 1227000 200 complete_chunk6135

lemma complete_chunk6136 : ∀ i : Fin 200, Compatible (1227200 + i.val) →
    (table.lookup (1227200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6136 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1227200 1227400 :=
  FiniteIntervals.of_fin 1227200 200 complete_chunk6136

lemma complete_chunk6137 : ∀ i : Fin 200, Compatible (1227400 + i.val) →
    (table.lookup (1227400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6137 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1227400 1227600 :=
  FiniteIntervals.of_fin 1227400 200 complete_chunk6137

lemma complete_chunk6138 : ∀ i : Fin 200, Compatible (1227600 + i.val) →
    (table.lookup (1227600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6138 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1227600 1227800 :=
  FiniteIntervals.of_fin 1227600 200 complete_chunk6138

lemma complete_chunk6139 : ∀ i : Fin 200, Compatible (1227800 + i.val) →
    (table.lookup (1227800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6139 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1227800 1228000 :=
  FiniteIntervals.of_fin 1227800 200 complete_chunk6139

#print axioms interval_chunk6130
end Erdos184Work.PureFiveFilter4
