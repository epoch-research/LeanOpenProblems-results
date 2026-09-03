import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5280 : ∀ i : Fin 200, Compatible (1056000 + i.val) →
    (table.lookup (1056000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5280 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1056000 1056200 :=
  FiniteIntervals.of_fin 1056000 200 complete_chunk5280

lemma complete_chunk5281 : ∀ i : Fin 200, Compatible (1056200 + i.val) →
    (table.lookup (1056200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5281 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1056200 1056400 :=
  FiniteIntervals.of_fin 1056200 200 complete_chunk5281

lemma complete_chunk5282 : ∀ i : Fin 200, Compatible (1056400 + i.val) →
    (table.lookup (1056400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5282 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1056400 1056600 :=
  FiniteIntervals.of_fin 1056400 200 complete_chunk5282

lemma complete_chunk5283 : ∀ i : Fin 200, Compatible (1056600 + i.val) →
    (table.lookup (1056600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5283 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1056600 1056800 :=
  FiniteIntervals.of_fin 1056600 200 complete_chunk5283

lemma complete_chunk5284 : ∀ i : Fin 200, Compatible (1056800 + i.val) →
    (table.lookup (1056800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5284 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1056800 1057000 :=
  FiniteIntervals.of_fin 1056800 200 complete_chunk5284

lemma complete_chunk5285 : ∀ i : Fin 200, Compatible (1057000 + i.val) →
    (table.lookup (1057000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5285 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1057000 1057200 :=
  FiniteIntervals.of_fin 1057000 200 complete_chunk5285

lemma complete_chunk5286 : ∀ i : Fin 200, Compatible (1057200 + i.val) →
    (table.lookup (1057200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5286 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1057200 1057400 :=
  FiniteIntervals.of_fin 1057200 200 complete_chunk5286

lemma complete_chunk5287 : ∀ i : Fin 200, Compatible (1057400 + i.val) →
    (table.lookup (1057400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5287 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1057400 1057600 :=
  FiniteIntervals.of_fin 1057400 200 complete_chunk5287

lemma complete_chunk5288 : ∀ i : Fin 200, Compatible (1057600 + i.val) →
    (table.lookup (1057600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5288 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1057600 1057800 :=
  FiniteIntervals.of_fin 1057600 200 complete_chunk5288

lemma complete_chunk5289 : ∀ i : Fin 200, Compatible (1057800 + i.val) →
    (table.lookup (1057800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5289 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1057800 1058000 :=
  FiniteIntervals.of_fin 1057800 200 complete_chunk5289

#print axioms interval_chunk5280
end Erdos184Work.PureFiveFilter4
