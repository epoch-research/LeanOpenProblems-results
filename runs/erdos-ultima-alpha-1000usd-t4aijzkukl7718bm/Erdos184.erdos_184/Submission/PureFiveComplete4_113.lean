import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1130 : ∀ i : Fin 200, Compatible (226000 + i.val) →
    (table.lookup (226000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1130 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 226000 226200 :=
  FiniteIntervals.of_fin 226000 200 complete_chunk1130

lemma complete_chunk1131 : ∀ i : Fin 200, Compatible (226200 + i.val) →
    (table.lookup (226200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1131 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 226200 226400 :=
  FiniteIntervals.of_fin 226200 200 complete_chunk1131

lemma complete_chunk1132 : ∀ i : Fin 200, Compatible (226400 + i.val) →
    (table.lookup (226400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1132 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 226400 226600 :=
  FiniteIntervals.of_fin 226400 200 complete_chunk1132

lemma complete_chunk1133 : ∀ i : Fin 200, Compatible (226600 + i.val) →
    (table.lookup (226600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1133 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 226600 226800 :=
  FiniteIntervals.of_fin 226600 200 complete_chunk1133

lemma complete_chunk1134 : ∀ i : Fin 200, Compatible (226800 + i.val) →
    (table.lookup (226800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1134 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 226800 227000 :=
  FiniteIntervals.of_fin 226800 200 complete_chunk1134

lemma complete_chunk1135 : ∀ i : Fin 200, Compatible (227000 + i.val) →
    (table.lookup (227000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1135 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 227000 227200 :=
  FiniteIntervals.of_fin 227000 200 complete_chunk1135

lemma complete_chunk1136 : ∀ i : Fin 200, Compatible (227200 + i.val) →
    (table.lookup (227200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1136 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 227200 227400 :=
  FiniteIntervals.of_fin 227200 200 complete_chunk1136

lemma complete_chunk1137 : ∀ i : Fin 200, Compatible (227400 + i.val) →
    (table.lookup (227400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1137 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 227400 227600 :=
  FiniteIntervals.of_fin 227400 200 complete_chunk1137

lemma complete_chunk1138 : ∀ i : Fin 200, Compatible (227600 + i.val) →
    (table.lookup (227600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1138 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 227600 227800 :=
  FiniteIntervals.of_fin 227600 200 complete_chunk1138

lemma complete_chunk1139 : ∀ i : Fin 200, Compatible (227800 + i.val) →
    (table.lookup (227800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1139 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 227800 228000 :=
  FiniteIntervals.of_fin 227800 200 complete_chunk1139

#print axioms interval_chunk1130
end Erdos184Work.PureFiveFilter4
