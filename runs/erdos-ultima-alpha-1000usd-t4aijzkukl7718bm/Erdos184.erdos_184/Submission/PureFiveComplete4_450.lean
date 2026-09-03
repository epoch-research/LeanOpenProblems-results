import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4500 : ∀ i : Fin 200, Compatible (900000 + i.val) →
    (table.lookup (900000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4500 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 900000 900200 :=
  FiniteIntervals.of_fin 900000 200 complete_chunk4500

lemma complete_chunk4501 : ∀ i : Fin 200, Compatible (900200 + i.val) →
    (table.lookup (900200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4501 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 900200 900400 :=
  FiniteIntervals.of_fin 900200 200 complete_chunk4501

lemma complete_chunk4502 : ∀ i : Fin 200, Compatible (900400 + i.val) →
    (table.lookup (900400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4502 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 900400 900600 :=
  FiniteIntervals.of_fin 900400 200 complete_chunk4502

lemma complete_chunk4503 : ∀ i : Fin 200, Compatible (900600 + i.val) →
    (table.lookup (900600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4503 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 900600 900800 :=
  FiniteIntervals.of_fin 900600 200 complete_chunk4503

lemma complete_chunk4504 : ∀ i : Fin 200, Compatible (900800 + i.val) →
    (table.lookup (900800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4504 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 900800 901000 :=
  FiniteIntervals.of_fin 900800 200 complete_chunk4504

lemma complete_chunk4505 : ∀ i : Fin 200, Compatible (901000 + i.val) →
    (table.lookup (901000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4505 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 901000 901200 :=
  FiniteIntervals.of_fin 901000 200 complete_chunk4505

lemma complete_chunk4506 : ∀ i : Fin 200, Compatible (901200 + i.val) →
    (table.lookup (901200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4506 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 901200 901400 :=
  FiniteIntervals.of_fin 901200 200 complete_chunk4506

lemma complete_chunk4507 : ∀ i : Fin 200, Compatible (901400 + i.val) →
    (table.lookup (901400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4507 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 901400 901600 :=
  FiniteIntervals.of_fin 901400 200 complete_chunk4507

lemma complete_chunk4508 : ∀ i : Fin 200, Compatible (901600 + i.val) →
    (table.lookup (901600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4508 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 901600 901800 :=
  FiniteIntervals.of_fin 901600 200 complete_chunk4508

lemma complete_chunk4509 : ∀ i : Fin 200, Compatible (901800 + i.val) →
    (table.lookup (901800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4509 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 901800 902000 :=
  FiniteIntervals.of_fin 901800 200 complete_chunk4509

#print axioms interval_chunk4500
end Erdos184Work.PureFiveFilter4
