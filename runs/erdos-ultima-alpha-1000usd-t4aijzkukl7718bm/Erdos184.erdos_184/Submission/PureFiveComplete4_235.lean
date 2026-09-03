import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2350 : ∀ i : Fin 200, Compatible (470000 + i.val) →
    (table.lookup (470000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2350 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 470000 470200 :=
  FiniteIntervals.of_fin 470000 200 complete_chunk2350

lemma complete_chunk2351 : ∀ i : Fin 200, Compatible (470200 + i.val) →
    (table.lookup (470200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2351 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 470200 470400 :=
  FiniteIntervals.of_fin 470200 200 complete_chunk2351

lemma complete_chunk2352 : ∀ i : Fin 200, Compatible (470400 + i.val) →
    (table.lookup (470400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2352 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 470400 470600 :=
  FiniteIntervals.of_fin 470400 200 complete_chunk2352

lemma complete_chunk2353 : ∀ i : Fin 200, Compatible (470600 + i.val) →
    (table.lookup (470600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2353 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 470600 470800 :=
  FiniteIntervals.of_fin 470600 200 complete_chunk2353

lemma complete_chunk2354 : ∀ i : Fin 200, Compatible (470800 + i.val) →
    (table.lookup (470800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2354 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 470800 471000 :=
  FiniteIntervals.of_fin 470800 200 complete_chunk2354

lemma complete_chunk2355 : ∀ i : Fin 200, Compatible (471000 + i.val) →
    (table.lookup (471000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2355 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 471000 471200 :=
  FiniteIntervals.of_fin 471000 200 complete_chunk2355

lemma complete_chunk2356 : ∀ i : Fin 200, Compatible (471200 + i.val) →
    (table.lookup (471200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2356 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 471200 471400 :=
  FiniteIntervals.of_fin 471200 200 complete_chunk2356

lemma complete_chunk2357 : ∀ i : Fin 200, Compatible (471400 + i.val) →
    (table.lookup (471400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2357 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 471400 471600 :=
  FiniteIntervals.of_fin 471400 200 complete_chunk2357

lemma complete_chunk2358 : ∀ i : Fin 200, Compatible (471600 + i.val) →
    (table.lookup (471600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2358 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 471600 471800 :=
  FiniteIntervals.of_fin 471600 200 complete_chunk2358

lemma complete_chunk2359 : ∀ i : Fin 200, Compatible (471800 + i.val) →
    (table.lookup (471800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2359 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 471800 472000 :=
  FiniteIntervals.of_fin 471800 200 complete_chunk2359

#print axioms interval_chunk2350
end Erdos184Work.PureFiveFilter4
