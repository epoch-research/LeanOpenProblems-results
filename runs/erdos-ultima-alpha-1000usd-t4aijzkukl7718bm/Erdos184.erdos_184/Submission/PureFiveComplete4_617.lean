import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6170 : ∀ i : Fin 200, Compatible (1234000 + i.val) →
    (table.lookup (1234000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6170 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1234000 1234200 :=
  FiniteIntervals.of_fin 1234000 200 complete_chunk6170

lemma complete_chunk6171 : ∀ i : Fin 200, Compatible (1234200 + i.val) →
    (table.lookup (1234200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6171 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1234200 1234400 :=
  FiniteIntervals.of_fin 1234200 200 complete_chunk6171

lemma complete_chunk6172 : ∀ i : Fin 200, Compatible (1234400 + i.val) →
    (table.lookup (1234400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6172 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1234400 1234600 :=
  FiniteIntervals.of_fin 1234400 200 complete_chunk6172

lemma complete_chunk6173 : ∀ i : Fin 200, Compatible (1234600 + i.val) →
    (table.lookup (1234600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6173 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1234600 1234800 :=
  FiniteIntervals.of_fin 1234600 200 complete_chunk6173

lemma complete_chunk6174 : ∀ i : Fin 200, Compatible (1234800 + i.val) →
    (table.lookup (1234800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6174 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1234800 1235000 :=
  FiniteIntervals.of_fin 1234800 200 complete_chunk6174

lemma complete_chunk6175 : ∀ i : Fin 200, Compatible (1235000 + i.val) →
    (table.lookup (1235000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6175 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1235000 1235200 :=
  FiniteIntervals.of_fin 1235000 200 complete_chunk6175

lemma complete_chunk6176 : ∀ i : Fin 200, Compatible (1235200 + i.val) →
    (table.lookup (1235200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6176 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1235200 1235400 :=
  FiniteIntervals.of_fin 1235200 200 complete_chunk6176

lemma complete_chunk6177 : ∀ i : Fin 200, Compatible (1235400 + i.val) →
    (table.lookup (1235400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6177 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1235400 1235600 :=
  FiniteIntervals.of_fin 1235400 200 complete_chunk6177

lemma complete_chunk6178 : ∀ i : Fin 200, Compatible (1235600 + i.val) →
    (table.lookup (1235600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6178 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1235600 1235800 :=
  FiniteIntervals.of_fin 1235600 200 complete_chunk6178

lemma complete_chunk6179 : ∀ i : Fin 200, Compatible (1235800 + i.val) →
    (table.lookup (1235800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6179 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1235800 1236000 :=
  FiniteIntervals.of_fin 1235800 200 complete_chunk6179

#print axioms interval_chunk6170
end Erdos184Work.PureFiveFilter4
