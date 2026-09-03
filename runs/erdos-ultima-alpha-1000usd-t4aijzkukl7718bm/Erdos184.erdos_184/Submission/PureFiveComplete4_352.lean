import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3520 : ∀ i : Fin 200, Compatible (704000 + i.val) →
    (table.lookup (704000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3520 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 704000 704200 :=
  FiniteIntervals.of_fin 704000 200 complete_chunk3520

lemma complete_chunk3521 : ∀ i : Fin 200, Compatible (704200 + i.val) →
    (table.lookup (704200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3521 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 704200 704400 :=
  FiniteIntervals.of_fin 704200 200 complete_chunk3521

lemma complete_chunk3522 : ∀ i : Fin 200, Compatible (704400 + i.val) →
    (table.lookup (704400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3522 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 704400 704600 :=
  FiniteIntervals.of_fin 704400 200 complete_chunk3522

lemma complete_chunk3523 : ∀ i : Fin 200, Compatible (704600 + i.val) →
    (table.lookup (704600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3523 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 704600 704800 :=
  FiniteIntervals.of_fin 704600 200 complete_chunk3523

lemma complete_chunk3524 : ∀ i : Fin 200, Compatible (704800 + i.val) →
    (table.lookup (704800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3524 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 704800 705000 :=
  FiniteIntervals.of_fin 704800 200 complete_chunk3524

lemma complete_chunk3525 : ∀ i : Fin 200, Compatible (705000 + i.val) →
    (table.lookup (705000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3525 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 705000 705200 :=
  FiniteIntervals.of_fin 705000 200 complete_chunk3525

lemma complete_chunk3526 : ∀ i : Fin 200, Compatible (705200 + i.val) →
    (table.lookup (705200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3526 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 705200 705400 :=
  FiniteIntervals.of_fin 705200 200 complete_chunk3526

lemma complete_chunk3527 : ∀ i : Fin 200, Compatible (705400 + i.val) →
    (table.lookup (705400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3527 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 705400 705600 :=
  FiniteIntervals.of_fin 705400 200 complete_chunk3527

lemma complete_chunk3528 : ∀ i : Fin 200, Compatible (705600 + i.val) →
    (table.lookup (705600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3528 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 705600 705800 :=
  FiniteIntervals.of_fin 705600 200 complete_chunk3528

lemma complete_chunk3529 : ∀ i : Fin 200, Compatible (705800 + i.val) →
    (table.lookup (705800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3529 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 705800 706000 :=
  FiniteIntervals.of_fin 705800 200 complete_chunk3529

#print axioms interval_chunk3520
end Erdos184Work.PureFiveFilter4
