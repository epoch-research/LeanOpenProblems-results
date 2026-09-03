import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5790 : ∀ i : Fin 200, Compatible (1158000 + i.val) →
    (table.lookup (1158000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5790 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1158000 1158200 :=
  FiniteIntervals.of_fin 1158000 200 complete_chunk5790

lemma complete_chunk5791 : ∀ i : Fin 200, Compatible (1158200 + i.val) →
    (table.lookup (1158200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5791 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1158200 1158400 :=
  FiniteIntervals.of_fin 1158200 200 complete_chunk5791

lemma complete_chunk5792 : ∀ i : Fin 200, Compatible (1158400 + i.val) →
    (table.lookup (1158400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5792 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1158400 1158600 :=
  FiniteIntervals.of_fin 1158400 200 complete_chunk5792

lemma complete_chunk5793 : ∀ i : Fin 200, Compatible (1158600 + i.val) →
    (table.lookup (1158600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5793 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1158600 1158800 :=
  FiniteIntervals.of_fin 1158600 200 complete_chunk5793

lemma complete_chunk5794 : ∀ i : Fin 200, Compatible (1158800 + i.val) →
    (table.lookup (1158800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5794 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1158800 1159000 :=
  FiniteIntervals.of_fin 1158800 200 complete_chunk5794

lemma complete_chunk5795 : ∀ i : Fin 200, Compatible (1159000 + i.val) →
    (table.lookup (1159000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5795 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1159000 1159200 :=
  FiniteIntervals.of_fin 1159000 200 complete_chunk5795

lemma complete_chunk5796 : ∀ i : Fin 200, Compatible (1159200 + i.val) →
    (table.lookup (1159200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5796 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1159200 1159400 :=
  FiniteIntervals.of_fin 1159200 200 complete_chunk5796

lemma complete_chunk5797 : ∀ i : Fin 200, Compatible (1159400 + i.val) →
    (table.lookup (1159400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5797 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1159400 1159600 :=
  FiniteIntervals.of_fin 1159400 200 complete_chunk5797

lemma complete_chunk5798 : ∀ i : Fin 200, Compatible (1159600 + i.val) →
    (table.lookup (1159600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5798 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1159600 1159800 :=
  FiniteIntervals.of_fin 1159600 200 complete_chunk5798

lemma complete_chunk5799 : ∀ i : Fin 200, Compatible (1159800 + i.val) →
    (table.lookup (1159800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5799 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1159800 1160000 :=
  FiniteIntervals.of_fin 1159800 200 complete_chunk5799

#print axioms interval_chunk5790
end Erdos184Work.PureFiveFilter4
