import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk790 : ∀ i : Fin 200, Compatible (158000 + i.val) →
    (table.lookup (158000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk790 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 158000 158200 :=
  FiniteIntervals.of_fin 158000 200 complete_chunk790

lemma complete_chunk791 : ∀ i : Fin 200, Compatible (158200 + i.val) →
    (table.lookup (158200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk791 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 158200 158400 :=
  FiniteIntervals.of_fin 158200 200 complete_chunk791

lemma complete_chunk792 : ∀ i : Fin 200, Compatible (158400 + i.val) →
    (table.lookup (158400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk792 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 158400 158600 :=
  FiniteIntervals.of_fin 158400 200 complete_chunk792

lemma complete_chunk793 : ∀ i : Fin 200, Compatible (158600 + i.val) →
    (table.lookup (158600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk793 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 158600 158800 :=
  FiniteIntervals.of_fin 158600 200 complete_chunk793

lemma complete_chunk794 : ∀ i : Fin 200, Compatible (158800 + i.val) →
    (table.lookup (158800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk794 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 158800 159000 :=
  FiniteIntervals.of_fin 158800 200 complete_chunk794

lemma complete_chunk795 : ∀ i : Fin 200, Compatible (159000 + i.val) →
    (table.lookup (159000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk795 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 159000 159200 :=
  FiniteIntervals.of_fin 159000 200 complete_chunk795

lemma complete_chunk796 : ∀ i : Fin 200, Compatible (159200 + i.val) →
    (table.lookup (159200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk796 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 159200 159400 :=
  FiniteIntervals.of_fin 159200 200 complete_chunk796

lemma complete_chunk797 : ∀ i : Fin 200, Compatible (159400 + i.val) →
    (table.lookup (159400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk797 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 159400 159600 :=
  FiniteIntervals.of_fin 159400 200 complete_chunk797

lemma complete_chunk798 : ∀ i : Fin 200, Compatible (159600 + i.val) →
    (table.lookup (159600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk798 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 159600 159800 :=
  FiniteIntervals.of_fin 159600 200 complete_chunk798

lemma complete_chunk799 : ∀ i : Fin 200, Compatible (159800 + i.val) →
    (table.lookup (159800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk799 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 159800 160000 :=
  FiniteIntervals.of_fin 159800 200 complete_chunk799

#print axioms interval_chunk790
end Erdos184Work.PureFiveFilter4
