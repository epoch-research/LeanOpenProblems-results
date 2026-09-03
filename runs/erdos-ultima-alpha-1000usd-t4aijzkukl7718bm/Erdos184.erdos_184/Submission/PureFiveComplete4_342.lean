import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3420 : ∀ i : Fin 200, Compatible (684000 + i.val) →
    (table.lookup (684000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3420 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 684000 684200 :=
  FiniteIntervals.of_fin 684000 200 complete_chunk3420

lemma complete_chunk3421 : ∀ i : Fin 200, Compatible (684200 + i.val) →
    (table.lookup (684200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3421 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 684200 684400 :=
  FiniteIntervals.of_fin 684200 200 complete_chunk3421

lemma complete_chunk3422 : ∀ i : Fin 200, Compatible (684400 + i.val) →
    (table.lookup (684400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3422 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 684400 684600 :=
  FiniteIntervals.of_fin 684400 200 complete_chunk3422

lemma complete_chunk3423 : ∀ i : Fin 200, Compatible (684600 + i.val) →
    (table.lookup (684600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3423 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 684600 684800 :=
  FiniteIntervals.of_fin 684600 200 complete_chunk3423

lemma complete_chunk3424 : ∀ i : Fin 200, Compatible (684800 + i.val) →
    (table.lookup (684800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3424 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 684800 685000 :=
  FiniteIntervals.of_fin 684800 200 complete_chunk3424

lemma complete_chunk3425 : ∀ i : Fin 200, Compatible (685000 + i.val) →
    (table.lookup (685000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3425 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 685000 685200 :=
  FiniteIntervals.of_fin 685000 200 complete_chunk3425

lemma complete_chunk3426 : ∀ i : Fin 200, Compatible (685200 + i.val) →
    (table.lookup (685200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3426 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 685200 685400 :=
  FiniteIntervals.of_fin 685200 200 complete_chunk3426

lemma complete_chunk3427 : ∀ i : Fin 200, Compatible (685400 + i.val) →
    (table.lookup (685400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3427 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 685400 685600 :=
  FiniteIntervals.of_fin 685400 200 complete_chunk3427

lemma complete_chunk3428 : ∀ i : Fin 200, Compatible (685600 + i.val) →
    (table.lookup (685600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3428 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 685600 685800 :=
  FiniteIntervals.of_fin 685600 200 complete_chunk3428

lemma complete_chunk3429 : ∀ i : Fin 200, Compatible (685800 + i.val) →
    (table.lookup (685800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3429 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 685800 686000 :=
  FiniteIntervals.of_fin 685800 200 complete_chunk3429

#print axioms interval_chunk3420
end Erdos184Work.PureFiveFilter4
