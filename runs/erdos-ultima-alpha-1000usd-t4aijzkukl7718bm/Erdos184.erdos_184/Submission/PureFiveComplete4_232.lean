import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2320 : ∀ i : Fin 200, Compatible (464000 + i.val) →
    (table.lookup (464000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2320 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 464000 464200 :=
  FiniteIntervals.of_fin 464000 200 complete_chunk2320

lemma complete_chunk2321 : ∀ i : Fin 200, Compatible (464200 + i.val) →
    (table.lookup (464200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2321 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 464200 464400 :=
  FiniteIntervals.of_fin 464200 200 complete_chunk2321

lemma complete_chunk2322 : ∀ i : Fin 200, Compatible (464400 + i.val) →
    (table.lookup (464400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2322 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 464400 464600 :=
  FiniteIntervals.of_fin 464400 200 complete_chunk2322

lemma complete_chunk2323 : ∀ i : Fin 200, Compatible (464600 + i.val) →
    (table.lookup (464600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2323 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 464600 464800 :=
  FiniteIntervals.of_fin 464600 200 complete_chunk2323

lemma complete_chunk2324 : ∀ i : Fin 200, Compatible (464800 + i.val) →
    (table.lookup (464800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2324 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 464800 465000 :=
  FiniteIntervals.of_fin 464800 200 complete_chunk2324

lemma complete_chunk2325 : ∀ i : Fin 200, Compatible (465000 + i.val) →
    (table.lookup (465000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2325 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 465000 465200 :=
  FiniteIntervals.of_fin 465000 200 complete_chunk2325

lemma complete_chunk2326 : ∀ i : Fin 200, Compatible (465200 + i.val) →
    (table.lookup (465200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2326 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 465200 465400 :=
  FiniteIntervals.of_fin 465200 200 complete_chunk2326

lemma complete_chunk2327 : ∀ i : Fin 200, Compatible (465400 + i.val) →
    (table.lookup (465400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2327 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 465400 465600 :=
  FiniteIntervals.of_fin 465400 200 complete_chunk2327

lemma complete_chunk2328 : ∀ i : Fin 200, Compatible (465600 + i.val) →
    (table.lookup (465600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2328 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 465600 465800 :=
  FiniteIntervals.of_fin 465600 200 complete_chunk2328

lemma complete_chunk2329 : ∀ i : Fin 200, Compatible (465800 + i.val) →
    (table.lookup (465800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2329 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 465800 466000 :=
  FiniteIntervals.of_fin 465800 200 complete_chunk2329

#print axioms interval_chunk2320
end Erdos184Work.PureFiveFilter4
