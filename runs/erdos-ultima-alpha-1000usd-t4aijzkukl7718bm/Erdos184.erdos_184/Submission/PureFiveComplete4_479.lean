import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4790 : ∀ i : Fin 200, Compatible (958000 + i.val) →
    (table.lookup (958000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4790 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 958000 958200 :=
  FiniteIntervals.of_fin 958000 200 complete_chunk4790

lemma complete_chunk4791 : ∀ i : Fin 200, Compatible (958200 + i.val) →
    (table.lookup (958200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4791 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 958200 958400 :=
  FiniteIntervals.of_fin 958200 200 complete_chunk4791

lemma complete_chunk4792 : ∀ i : Fin 200, Compatible (958400 + i.val) →
    (table.lookup (958400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4792 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 958400 958600 :=
  FiniteIntervals.of_fin 958400 200 complete_chunk4792

lemma complete_chunk4793 : ∀ i : Fin 200, Compatible (958600 + i.val) →
    (table.lookup (958600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4793 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 958600 958800 :=
  FiniteIntervals.of_fin 958600 200 complete_chunk4793

lemma complete_chunk4794 : ∀ i : Fin 200, Compatible (958800 + i.val) →
    (table.lookup (958800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4794 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 958800 959000 :=
  FiniteIntervals.of_fin 958800 200 complete_chunk4794

lemma complete_chunk4795 : ∀ i : Fin 200, Compatible (959000 + i.val) →
    (table.lookup (959000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4795 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 959000 959200 :=
  FiniteIntervals.of_fin 959000 200 complete_chunk4795

lemma complete_chunk4796 : ∀ i : Fin 200, Compatible (959200 + i.val) →
    (table.lookup (959200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4796 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 959200 959400 :=
  FiniteIntervals.of_fin 959200 200 complete_chunk4796

lemma complete_chunk4797 : ∀ i : Fin 200, Compatible (959400 + i.val) →
    (table.lookup (959400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4797 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 959400 959600 :=
  FiniteIntervals.of_fin 959400 200 complete_chunk4797

lemma complete_chunk4798 : ∀ i : Fin 200, Compatible (959600 + i.val) →
    (table.lookup (959600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4798 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 959600 959800 :=
  FiniteIntervals.of_fin 959600 200 complete_chunk4798

lemma complete_chunk4799 : ∀ i : Fin 200, Compatible (959800 + i.val) →
    (table.lookup (959800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4799 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 959800 960000 :=
  FiniteIntervals.of_fin 959800 200 complete_chunk4799

#print axioms interval_chunk4790
end Erdos184Work.PureFiveFilter4
