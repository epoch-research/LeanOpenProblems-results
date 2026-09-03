import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3780 : ∀ i : Fin 200, Compatible (756000 + i.val) →
    (table.lookup (756000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3780 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 756000 756200 :=
  FiniteIntervals.of_fin 756000 200 complete_chunk3780

lemma complete_chunk3781 : ∀ i : Fin 200, Compatible (756200 + i.val) →
    (table.lookup (756200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3781 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 756200 756400 :=
  FiniteIntervals.of_fin 756200 200 complete_chunk3781

lemma complete_chunk3782 : ∀ i : Fin 200, Compatible (756400 + i.val) →
    (table.lookup (756400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3782 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 756400 756600 :=
  FiniteIntervals.of_fin 756400 200 complete_chunk3782

lemma complete_chunk3783 : ∀ i : Fin 200, Compatible (756600 + i.val) →
    (table.lookup (756600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3783 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 756600 756800 :=
  FiniteIntervals.of_fin 756600 200 complete_chunk3783

lemma complete_chunk3784 : ∀ i : Fin 200, Compatible (756800 + i.val) →
    (table.lookup (756800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3784 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 756800 757000 :=
  FiniteIntervals.of_fin 756800 200 complete_chunk3784

lemma complete_chunk3785 : ∀ i : Fin 200, Compatible (757000 + i.val) →
    (table.lookup (757000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3785 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 757000 757200 :=
  FiniteIntervals.of_fin 757000 200 complete_chunk3785

lemma complete_chunk3786 : ∀ i : Fin 200, Compatible (757200 + i.val) →
    (table.lookup (757200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3786 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 757200 757400 :=
  FiniteIntervals.of_fin 757200 200 complete_chunk3786

lemma complete_chunk3787 : ∀ i : Fin 200, Compatible (757400 + i.val) →
    (table.lookup (757400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3787 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 757400 757600 :=
  FiniteIntervals.of_fin 757400 200 complete_chunk3787

lemma complete_chunk3788 : ∀ i : Fin 200, Compatible (757600 + i.val) →
    (table.lookup (757600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3788 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 757600 757800 :=
  FiniteIntervals.of_fin 757600 200 complete_chunk3788

lemma complete_chunk3789 : ∀ i : Fin 200, Compatible (757800 + i.val) →
    (table.lookup (757800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3789 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 757800 758000 :=
  FiniteIntervals.of_fin 757800 200 complete_chunk3789

#print axioms interval_chunk3780
end Erdos184Work.PureFiveFilter4
