import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5390 : ∀ i : Fin 200, Compatible (1078000 + i.val) →
    (table.lookup (1078000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5390 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1078000 1078200 :=
  FiniteIntervals.of_fin 1078000 200 complete_chunk5390

lemma complete_chunk5391 : ∀ i : Fin 200, Compatible (1078200 + i.val) →
    (table.lookup (1078200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5391 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1078200 1078400 :=
  FiniteIntervals.of_fin 1078200 200 complete_chunk5391

lemma complete_chunk5392 : ∀ i : Fin 200, Compatible (1078400 + i.val) →
    (table.lookup (1078400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5392 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1078400 1078600 :=
  FiniteIntervals.of_fin 1078400 200 complete_chunk5392

lemma complete_chunk5393 : ∀ i : Fin 200, Compatible (1078600 + i.val) →
    (table.lookup (1078600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5393 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1078600 1078800 :=
  FiniteIntervals.of_fin 1078600 200 complete_chunk5393

lemma complete_chunk5394 : ∀ i : Fin 200, Compatible (1078800 + i.val) →
    (table.lookup (1078800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5394 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1078800 1079000 :=
  FiniteIntervals.of_fin 1078800 200 complete_chunk5394

lemma complete_chunk5395 : ∀ i : Fin 200, Compatible (1079000 + i.val) →
    (table.lookup (1079000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5395 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1079000 1079200 :=
  FiniteIntervals.of_fin 1079000 200 complete_chunk5395

lemma complete_chunk5396 : ∀ i : Fin 200, Compatible (1079200 + i.val) →
    (table.lookup (1079200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5396 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1079200 1079400 :=
  FiniteIntervals.of_fin 1079200 200 complete_chunk5396

lemma complete_chunk5397 : ∀ i : Fin 200, Compatible (1079400 + i.val) →
    (table.lookup (1079400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5397 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1079400 1079600 :=
  FiniteIntervals.of_fin 1079400 200 complete_chunk5397

lemma complete_chunk5398 : ∀ i : Fin 200, Compatible (1079600 + i.val) →
    (table.lookup (1079600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5398 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1079600 1079800 :=
  FiniteIntervals.of_fin 1079600 200 complete_chunk5398

lemma complete_chunk5399 : ∀ i : Fin 200, Compatible (1079800 + i.val) →
    (table.lookup (1079800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5399 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1079800 1080000 :=
  FiniteIntervals.of_fin 1079800 200 complete_chunk5399

#print axioms interval_chunk5390
end Erdos184Work.PureFiveFilter4
