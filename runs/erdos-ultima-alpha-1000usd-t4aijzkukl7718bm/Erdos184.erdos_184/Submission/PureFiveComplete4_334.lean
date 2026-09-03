import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3340 : ∀ i : Fin 200, Compatible (668000 + i.val) →
    (table.lookup (668000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3340 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 668000 668200 :=
  FiniteIntervals.of_fin 668000 200 complete_chunk3340

lemma complete_chunk3341 : ∀ i : Fin 200, Compatible (668200 + i.val) →
    (table.lookup (668200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3341 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 668200 668400 :=
  FiniteIntervals.of_fin 668200 200 complete_chunk3341

lemma complete_chunk3342 : ∀ i : Fin 200, Compatible (668400 + i.val) →
    (table.lookup (668400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3342 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 668400 668600 :=
  FiniteIntervals.of_fin 668400 200 complete_chunk3342

lemma complete_chunk3343 : ∀ i : Fin 200, Compatible (668600 + i.val) →
    (table.lookup (668600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3343 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 668600 668800 :=
  FiniteIntervals.of_fin 668600 200 complete_chunk3343

lemma complete_chunk3344 : ∀ i : Fin 200, Compatible (668800 + i.val) →
    (table.lookup (668800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3344 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 668800 669000 :=
  FiniteIntervals.of_fin 668800 200 complete_chunk3344

lemma complete_chunk3345 : ∀ i : Fin 200, Compatible (669000 + i.val) →
    (table.lookup (669000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3345 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 669000 669200 :=
  FiniteIntervals.of_fin 669000 200 complete_chunk3345

lemma complete_chunk3346 : ∀ i : Fin 200, Compatible (669200 + i.val) →
    (table.lookup (669200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3346 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 669200 669400 :=
  FiniteIntervals.of_fin 669200 200 complete_chunk3346

lemma complete_chunk3347 : ∀ i : Fin 200, Compatible (669400 + i.val) →
    (table.lookup (669400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3347 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 669400 669600 :=
  FiniteIntervals.of_fin 669400 200 complete_chunk3347

lemma complete_chunk3348 : ∀ i : Fin 200, Compatible (669600 + i.val) →
    (table.lookup (669600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3348 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 669600 669800 :=
  FiniteIntervals.of_fin 669600 200 complete_chunk3348

lemma complete_chunk3349 : ∀ i : Fin 200, Compatible (669800 + i.val) →
    (table.lookup (669800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3349 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 669800 670000 :=
  FiniteIntervals.of_fin 669800 200 complete_chunk3349

#print axioms interval_chunk3340
end Erdos184Work.PureFiveFilter4
