import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3290 : ∀ i : Fin 200, Compatible (658000 + i.val) →
    (table.lookup (658000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3290 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 658000 658200 :=
  FiniteIntervals.of_fin 658000 200 complete_chunk3290

lemma complete_chunk3291 : ∀ i : Fin 200, Compatible (658200 + i.val) →
    (table.lookup (658200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3291 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 658200 658400 :=
  FiniteIntervals.of_fin 658200 200 complete_chunk3291

lemma complete_chunk3292 : ∀ i : Fin 200, Compatible (658400 + i.val) →
    (table.lookup (658400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3292 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 658400 658600 :=
  FiniteIntervals.of_fin 658400 200 complete_chunk3292

lemma complete_chunk3293 : ∀ i : Fin 200, Compatible (658600 + i.val) →
    (table.lookup (658600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3293 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 658600 658800 :=
  FiniteIntervals.of_fin 658600 200 complete_chunk3293

lemma complete_chunk3294 : ∀ i : Fin 200, Compatible (658800 + i.val) →
    (table.lookup (658800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3294 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 658800 659000 :=
  FiniteIntervals.of_fin 658800 200 complete_chunk3294

lemma complete_chunk3295 : ∀ i : Fin 200, Compatible (659000 + i.val) →
    (table.lookup (659000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3295 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 659000 659200 :=
  FiniteIntervals.of_fin 659000 200 complete_chunk3295

lemma complete_chunk3296 : ∀ i : Fin 200, Compatible (659200 + i.val) →
    (table.lookup (659200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3296 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 659200 659400 :=
  FiniteIntervals.of_fin 659200 200 complete_chunk3296

lemma complete_chunk3297 : ∀ i : Fin 200, Compatible (659400 + i.val) →
    (table.lookup (659400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3297 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 659400 659600 :=
  FiniteIntervals.of_fin 659400 200 complete_chunk3297

lemma complete_chunk3298 : ∀ i : Fin 200, Compatible (659600 + i.val) →
    (table.lookup (659600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3298 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 659600 659800 :=
  FiniteIntervals.of_fin 659600 200 complete_chunk3298

lemma complete_chunk3299 : ∀ i : Fin 200, Compatible (659800 + i.val) →
    (table.lookup (659800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3299 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 659800 660000 :=
  FiniteIntervals.of_fin 659800 200 complete_chunk3299

#print axioms interval_chunk3290
end Erdos184Work.PureFiveFilter4
