import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2770 : ∀ i : Fin 200, Compatible (554000 + i.val) →
    (table.lookup (554000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2770 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 554000 554200 :=
  FiniteIntervals.of_fin 554000 200 complete_chunk2770

lemma complete_chunk2771 : ∀ i : Fin 200, Compatible (554200 + i.val) →
    (table.lookup (554200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2771 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 554200 554400 :=
  FiniteIntervals.of_fin 554200 200 complete_chunk2771

lemma complete_chunk2772 : ∀ i : Fin 200, Compatible (554400 + i.val) →
    (table.lookup (554400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2772 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 554400 554600 :=
  FiniteIntervals.of_fin 554400 200 complete_chunk2772

lemma complete_chunk2773 : ∀ i : Fin 200, Compatible (554600 + i.val) →
    (table.lookup (554600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2773 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 554600 554800 :=
  FiniteIntervals.of_fin 554600 200 complete_chunk2773

lemma complete_chunk2774 : ∀ i : Fin 200, Compatible (554800 + i.val) →
    (table.lookup (554800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2774 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 554800 555000 :=
  FiniteIntervals.of_fin 554800 200 complete_chunk2774

lemma complete_chunk2775 : ∀ i : Fin 200, Compatible (555000 + i.val) →
    (table.lookup (555000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2775 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 555000 555200 :=
  FiniteIntervals.of_fin 555000 200 complete_chunk2775

lemma complete_chunk2776 : ∀ i : Fin 200, Compatible (555200 + i.val) →
    (table.lookup (555200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2776 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 555200 555400 :=
  FiniteIntervals.of_fin 555200 200 complete_chunk2776

lemma complete_chunk2777 : ∀ i : Fin 200, Compatible (555400 + i.val) →
    (table.lookup (555400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2777 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 555400 555600 :=
  FiniteIntervals.of_fin 555400 200 complete_chunk2777

lemma complete_chunk2778 : ∀ i : Fin 200, Compatible (555600 + i.val) →
    (table.lookup (555600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2778 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 555600 555800 :=
  FiniteIntervals.of_fin 555600 200 complete_chunk2778

lemma complete_chunk2779 : ∀ i : Fin 200, Compatible (555800 + i.val) →
    (table.lookup (555800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2779 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 555800 556000 :=
  FiniteIntervals.of_fin 555800 200 complete_chunk2779

#print axioms interval_chunk2770
end Erdos184Work.PureFiveFilter4
