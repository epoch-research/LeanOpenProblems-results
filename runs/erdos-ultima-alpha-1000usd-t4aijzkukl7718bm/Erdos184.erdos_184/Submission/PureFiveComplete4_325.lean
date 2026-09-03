import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3250 : ∀ i : Fin 200, Compatible (650000 + i.val) →
    (table.lookup (650000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3250 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 650000 650200 :=
  FiniteIntervals.of_fin 650000 200 complete_chunk3250

lemma complete_chunk3251 : ∀ i : Fin 200, Compatible (650200 + i.val) →
    (table.lookup (650200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3251 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 650200 650400 :=
  FiniteIntervals.of_fin 650200 200 complete_chunk3251

lemma complete_chunk3252 : ∀ i : Fin 200, Compatible (650400 + i.val) →
    (table.lookup (650400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3252 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 650400 650600 :=
  FiniteIntervals.of_fin 650400 200 complete_chunk3252

lemma complete_chunk3253 : ∀ i : Fin 200, Compatible (650600 + i.val) →
    (table.lookup (650600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3253 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 650600 650800 :=
  FiniteIntervals.of_fin 650600 200 complete_chunk3253

lemma complete_chunk3254 : ∀ i : Fin 200, Compatible (650800 + i.val) →
    (table.lookup (650800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3254 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 650800 651000 :=
  FiniteIntervals.of_fin 650800 200 complete_chunk3254

lemma complete_chunk3255 : ∀ i : Fin 200, Compatible (651000 + i.val) →
    (table.lookup (651000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3255 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 651000 651200 :=
  FiniteIntervals.of_fin 651000 200 complete_chunk3255

lemma complete_chunk3256 : ∀ i : Fin 200, Compatible (651200 + i.val) →
    (table.lookup (651200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3256 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 651200 651400 :=
  FiniteIntervals.of_fin 651200 200 complete_chunk3256

lemma complete_chunk3257 : ∀ i : Fin 200, Compatible (651400 + i.val) →
    (table.lookup (651400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3257 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 651400 651600 :=
  FiniteIntervals.of_fin 651400 200 complete_chunk3257

lemma complete_chunk3258 : ∀ i : Fin 200, Compatible (651600 + i.val) →
    (table.lookup (651600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3258 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 651600 651800 :=
  FiniteIntervals.of_fin 651600 200 complete_chunk3258

lemma complete_chunk3259 : ∀ i : Fin 200, Compatible (651800 + i.val) →
    (table.lookup (651800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3259 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 651800 652000 :=
  FiniteIntervals.of_fin 651800 200 complete_chunk3259

#print axioms interval_chunk3250
end Erdos184Work.PureFiveFilter4
