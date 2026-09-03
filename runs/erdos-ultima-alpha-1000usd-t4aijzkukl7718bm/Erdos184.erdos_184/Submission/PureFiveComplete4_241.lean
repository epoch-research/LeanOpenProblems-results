import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2410 : ∀ i : Fin 200, Compatible (482000 + i.val) →
    (table.lookup (482000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2410 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 482000 482200 :=
  FiniteIntervals.of_fin 482000 200 complete_chunk2410

lemma complete_chunk2411 : ∀ i : Fin 200, Compatible (482200 + i.val) →
    (table.lookup (482200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2411 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 482200 482400 :=
  FiniteIntervals.of_fin 482200 200 complete_chunk2411

lemma complete_chunk2412 : ∀ i : Fin 200, Compatible (482400 + i.val) →
    (table.lookup (482400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2412 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 482400 482600 :=
  FiniteIntervals.of_fin 482400 200 complete_chunk2412

lemma complete_chunk2413 : ∀ i : Fin 200, Compatible (482600 + i.val) →
    (table.lookup (482600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2413 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 482600 482800 :=
  FiniteIntervals.of_fin 482600 200 complete_chunk2413

lemma complete_chunk2414 : ∀ i : Fin 200, Compatible (482800 + i.val) →
    (table.lookup (482800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2414 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 482800 483000 :=
  FiniteIntervals.of_fin 482800 200 complete_chunk2414

lemma complete_chunk2415 : ∀ i : Fin 200, Compatible (483000 + i.val) →
    (table.lookup (483000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2415 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 483000 483200 :=
  FiniteIntervals.of_fin 483000 200 complete_chunk2415

lemma complete_chunk2416 : ∀ i : Fin 200, Compatible (483200 + i.val) →
    (table.lookup (483200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2416 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 483200 483400 :=
  FiniteIntervals.of_fin 483200 200 complete_chunk2416

lemma complete_chunk2417 : ∀ i : Fin 200, Compatible (483400 + i.val) →
    (table.lookup (483400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2417 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 483400 483600 :=
  FiniteIntervals.of_fin 483400 200 complete_chunk2417

lemma complete_chunk2418 : ∀ i : Fin 200, Compatible (483600 + i.val) →
    (table.lookup (483600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2418 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 483600 483800 :=
  FiniteIntervals.of_fin 483600 200 complete_chunk2418

lemma complete_chunk2419 : ∀ i : Fin 200, Compatible (483800 + i.val) →
    (table.lookup (483800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2419 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 483800 484000 :=
  FiniteIntervals.of_fin 483800 200 complete_chunk2419

#print axioms interval_chunk2410
end Erdos184Work.PureFiveFilter4
