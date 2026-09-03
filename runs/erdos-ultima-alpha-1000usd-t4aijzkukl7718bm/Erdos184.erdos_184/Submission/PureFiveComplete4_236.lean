import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2360 : ∀ i : Fin 200, Compatible (472000 + i.val) →
    (table.lookup (472000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2360 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 472000 472200 :=
  FiniteIntervals.of_fin 472000 200 complete_chunk2360

lemma complete_chunk2361 : ∀ i : Fin 200, Compatible (472200 + i.val) →
    (table.lookup (472200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2361 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 472200 472400 :=
  FiniteIntervals.of_fin 472200 200 complete_chunk2361

lemma complete_chunk2362 : ∀ i : Fin 200, Compatible (472400 + i.val) →
    (table.lookup (472400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2362 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 472400 472600 :=
  FiniteIntervals.of_fin 472400 200 complete_chunk2362

lemma complete_chunk2363 : ∀ i : Fin 200, Compatible (472600 + i.val) →
    (table.lookup (472600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2363 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 472600 472800 :=
  FiniteIntervals.of_fin 472600 200 complete_chunk2363

lemma complete_chunk2364 : ∀ i : Fin 200, Compatible (472800 + i.val) →
    (table.lookup (472800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2364 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 472800 473000 :=
  FiniteIntervals.of_fin 472800 200 complete_chunk2364

lemma complete_chunk2365 : ∀ i : Fin 200, Compatible (473000 + i.val) →
    (table.lookup (473000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2365 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 473000 473200 :=
  FiniteIntervals.of_fin 473000 200 complete_chunk2365

lemma complete_chunk2366 : ∀ i : Fin 200, Compatible (473200 + i.val) →
    (table.lookup (473200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2366 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 473200 473400 :=
  FiniteIntervals.of_fin 473200 200 complete_chunk2366

lemma complete_chunk2367 : ∀ i : Fin 200, Compatible (473400 + i.val) →
    (table.lookup (473400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2367 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 473400 473600 :=
  FiniteIntervals.of_fin 473400 200 complete_chunk2367

lemma complete_chunk2368 : ∀ i : Fin 200, Compatible (473600 + i.val) →
    (table.lookup (473600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2368 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 473600 473800 :=
  FiniteIntervals.of_fin 473600 200 complete_chunk2368

lemma complete_chunk2369 : ∀ i : Fin 200, Compatible (473800 + i.val) →
    (table.lookup (473800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2369 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 473800 474000 :=
  FiniteIntervals.of_fin 473800 200 complete_chunk2369

#print axioms interval_chunk2360
end Erdos184Work.PureFiveFilter4
