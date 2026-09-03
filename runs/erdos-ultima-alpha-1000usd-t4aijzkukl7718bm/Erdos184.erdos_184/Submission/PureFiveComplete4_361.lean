import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3610 : ∀ i : Fin 200, Compatible (722000 + i.val) →
    (table.lookup (722000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3610 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 722000 722200 :=
  FiniteIntervals.of_fin 722000 200 complete_chunk3610

lemma complete_chunk3611 : ∀ i : Fin 200, Compatible (722200 + i.val) →
    (table.lookup (722200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3611 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 722200 722400 :=
  FiniteIntervals.of_fin 722200 200 complete_chunk3611

lemma complete_chunk3612 : ∀ i : Fin 200, Compatible (722400 + i.val) →
    (table.lookup (722400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3612 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 722400 722600 :=
  FiniteIntervals.of_fin 722400 200 complete_chunk3612

lemma complete_chunk3613 : ∀ i : Fin 200, Compatible (722600 + i.val) →
    (table.lookup (722600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3613 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 722600 722800 :=
  FiniteIntervals.of_fin 722600 200 complete_chunk3613

lemma complete_chunk3614 : ∀ i : Fin 200, Compatible (722800 + i.val) →
    (table.lookup (722800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3614 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 722800 723000 :=
  FiniteIntervals.of_fin 722800 200 complete_chunk3614

lemma complete_chunk3615 : ∀ i : Fin 200, Compatible (723000 + i.val) →
    (table.lookup (723000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3615 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 723000 723200 :=
  FiniteIntervals.of_fin 723000 200 complete_chunk3615

lemma complete_chunk3616 : ∀ i : Fin 200, Compatible (723200 + i.val) →
    (table.lookup (723200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3616 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 723200 723400 :=
  FiniteIntervals.of_fin 723200 200 complete_chunk3616

lemma complete_chunk3617 : ∀ i : Fin 200, Compatible (723400 + i.val) →
    (table.lookup (723400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3617 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 723400 723600 :=
  FiniteIntervals.of_fin 723400 200 complete_chunk3617

lemma complete_chunk3618 : ∀ i : Fin 200, Compatible (723600 + i.val) →
    (table.lookup (723600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3618 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 723600 723800 :=
  FiniteIntervals.of_fin 723600 200 complete_chunk3618

lemma complete_chunk3619 : ∀ i : Fin 200, Compatible (723800 + i.val) →
    (table.lookup (723800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3619 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 723800 724000 :=
  FiniteIntervals.of_fin 723800 200 complete_chunk3619

#print axioms interval_chunk3610
end Erdos184Work.PureFiveFilter4
