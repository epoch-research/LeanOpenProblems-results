import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3680 : ∀ i : Fin 200, Compatible (736000 + i.val) →
    (table.lookup (736000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3680 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 736000 736200 :=
  FiniteIntervals.of_fin 736000 200 complete_chunk3680

lemma complete_chunk3681 : ∀ i : Fin 200, Compatible (736200 + i.val) →
    (table.lookup (736200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3681 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 736200 736400 :=
  FiniteIntervals.of_fin 736200 200 complete_chunk3681

lemma complete_chunk3682 : ∀ i : Fin 200, Compatible (736400 + i.val) →
    (table.lookup (736400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3682 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 736400 736600 :=
  FiniteIntervals.of_fin 736400 200 complete_chunk3682

lemma complete_chunk3683 : ∀ i : Fin 200, Compatible (736600 + i.val) →
    (table.lookup (736600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3683 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 736600 736800 :=
  FiniteIntervals.of_fin 736600 200 complete_chunk3683

lemma complete_chunk3684 : ∀ i : Fin 200, Compatible (736800 + i.val) →
    (table.lookup (736800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3684 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 736800 737000 :=
  FiniteIntervals.of_fin 736800 200 complete_chunk3684

lemma complete_chunk3685 : ∀ i : Fin 200, Compatible (737000 + i.val) →
    (table.lookup (737000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3685 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 737000 737200 :=
  FiniteIntervals.of_fin 737000 200 complete_chunk3685

lemma complete_chunk3686 : ∀ i : Fin 200, Compatible (737200 + i.val) →
    (table.lookup (737200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3686 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 737200 737400 :=
  FiniteIntervals.of_fin 737200 200 complete_chunk3686

lemma complete_chunk3687 : ∀ i : Fin 200, Compatible (737400 + i.val) →
    (table.lookup (737400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3687 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 737400 737600 :=
  FiniteIntervals.of_fin 737400 200 complete_chunk3687

lemma complete_chunk3688 : ∀ i : Fin 200, Compatible (737600 + i.val) →
    (table.lookup (737600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3688 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 737600 737800 :=
  FiniteIntervals.of_fin 737600 200 complete_chunk3688

lemma complete_chunk3689 : ∀ i : Fin 200, Compatible (737800 + i.val) →
    (table.lookup (737800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3689 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 737800 738000 :=
  FiniteIntervals.of_fin 737800 200 complete_chunk3689

#print axioms interval_chunk3680
end Erdos184Work.PureFiveFilter4
