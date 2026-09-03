import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2340 : ∀ i : Fin 200, Compatible (468000 + i.val) →
    (table.lookup (468000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2340 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 468000 468200 :=
  FiniteIntervals.of_fin 468000 200 complete_chunk2340

lemma complete_chunk2341 : ∀ i : Fin 200, Compatible (468200 + i.val) →
    (table.lookup (468200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2341 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 468200 468400 :=
  FiniteIntervals.of_fin 468200 200 complete_chunk2341

lemma complete_chunk2342 : ∀ i : Fin 200, Compatible (468400 + i.val) →
    (table.lookup (468400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2342 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 468400 468600 :=
  FiniteIntervals.of_fin 468400 200 complete_chunk2342

lemma complete_chunk2343 : ∀ i : Fin 200, Compatible (468600 + i.val) →
    (table.lookup (468600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2343 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 468600 468800 :=
  FiniteIntervals.of_fin 468600 200 complete_chunk2343

lemma complete_chunk2344 : ∀ i : Fin 200, Compatible (468800 + i.val) →
    (table.lookup (468800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2344 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 468800 469000 :=
  FiniteIntervals.of_fin 468800 200 complete_chunk2344

lemma complete_chunk2345 : ∀ i : Fin 200, Compatible (469000 + i.val) →
    (table.lookup (469000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2345 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 469000 469200 :=
  FiniteIntervals.of_fin 469000 200 complete_chunk2345

lemma complete_chunk2346 : ∀ i : Fin 200, Compatible (469200 + i.val) →
    (table.lookup (469200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2346 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 469200 469400 :=
  FiniteIntervals.of_fin 469200 200 complete_chunk2346

lemma complete_chunk2347 : ∀ i : Fin 200, Compatible (469400 + i.val) →
    (table.lookup (469400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2347 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 469400 469600 :=
  FiniteIntervals.of_fin 469400 200 complete_chunk2347

lemma complete_chunk2348 : ∀ i : Fin 200, Compatible (469600 + i.val) →
    (table.lookup (469600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2348 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 469600 469800 :=
  FiniteIntervals.of_fin 469600 200 complete_chunk2348

lemma complete_chunk2349 : ∀ i : Fin 200, Compatible (469800 + i.val) →
    (table.lookup (469800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2349 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 469800 470000 :=
  FiniteIntervals.of_fin 469800 200 complete_chunk2349

#print axioms interval_chunk2340
end Erdos184Work.PureFiveFilter4
