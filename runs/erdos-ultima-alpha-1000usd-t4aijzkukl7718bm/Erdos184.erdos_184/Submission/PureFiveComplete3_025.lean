import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk250 : ∀ i : Fin 200, Compatible (50000 + i.val) →
    (table.lookup (50000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk250 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50000 50200 :=
  FiniteIntervals.of_fin 50000 200 complete_chunk250

lemma complete_chunk251 : ∀ i : Fin 200, Compatible (50200 + i.val) →
    (table.lookup (50200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk251 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50200 50400 :=
  FiniteIntervals.of_fin 50200 200 complete_chunk251

lemma complete_chunk252 : ∀ i : Fin 200, Compatible (50400 + i.val) →
    (table.lookup (50400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk252 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50400 50600 :=
  FiniteIntervals.of_fin 50400 200 complete_chunk252

lemma complete_chunk253 : ∀ i : Fin 200, Compatible (50600 + i.val) →
    (table.lookup (50600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk253 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50600 50800 :=
  FiniteIntervals.of_fin 50600 200 complete_chunk253

lemma complete_chunk254 : ∀ i : Fin 200, Compatible (50800 + i.val) →
    (table.lookup (50800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk254 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50800 51000 :=
  FiniteIntervals.of_fin 50800 200 complete_chunk254

lemma complete_chunk255 : ∀ i : Fin 200, Compatible (51000 + i.val) →
    (table.lookup (51000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk255 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51000 51200 :=
  FiniteIntervals.of_fin 51000 200 complete_chunk255

lemma complete_chunk256 : ∀ i : Fin 200, Compatible (51200 + i.val) →
    (table.lookup (51200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk256 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51200 51400 :=
  FiniteIntervals.of_fin 51200 200 complete_chunk256

lemma complete_chunk257 : ∀ i : Fin 200, Compatible (51400 + i.val) →
    (table.lookup (51400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk257 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51400 51600 :=
  FiniteIntervals.of_fin 51400 200 complete_chunk257

lemma complete_chunk258 : ∀ i : Fin 200, Compatible (51600 + i.val) →
    (table.lookup (51600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk258 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51600 51800 :=
  FiniteIntervals.of_fin 51600 200 complete_chunk258

lemma complete_chunk259 : ∀ i : Fin 200, Compatible (51800 + i.val) →
    (table.lookup (51800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk259 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51800 52000 :=
  FiniteIntervals.of_fin 51800 200 complete_chunk259

#print axioms interval_chunk250
end Erdos184Work.PureFiveFilter3
