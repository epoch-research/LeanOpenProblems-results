import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2820 : ∀ i : Fin 200, Compatible (564000 + i.val) →
    (table.lookup (564000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2820 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 564000 564200 :=
  FiniteIntervals.of_fin 564000 200 complete_chunk2820

lemma complete_chunk2821 : ∀ i : Fin 200, Compatible (564200 + i.val) →
    (table.lookup (564200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2821 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 564200 564400 :=
  FiniteIntervals.of_fin 564200 200 complete_chunk2821

lemma complete_chunk2822 : ∀ i : Fin 200, Compatible (564400 + i.val) →
    (table.lookup (564400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2822 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 564400 564600 :=
  FiniteIntervals.of_fin 564400 200 complete_chunk2822

lemma complete_chunk2823 : ∀ i : Fin 200, Compatible (564600 + i.val) →
    (table.lookup (564600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2823 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 564600 564800 :=
  FiniteIntervals.of_fin 564600 200 complete_chunk2823

lemma complete_chunk2824 : ∀ i : Fin 200, Compatible (564800 + i.val) →
    (table.lookup (564800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2824 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 564800 565000 :=
  FiniteIntervals.of_fin 564800 200 complete_chunk2824

lemma complete_chunk2825 : ∀ i : Fin 200, Compatible (565000 + i.val) →
    (table.lookup (565000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2825 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 565000 565200 :=
  FiniteIntervals.of_fin 565000 200 complete_chunk2825

lemma complete_chunk2826 : ∀ i : Fin 200, Compatible (565200 + i.val) →
    (table.lookup (565200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2826 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 565200 565400 :=
  FiniteIntervals.of_fin 565200 200 complete_chunk2826

lemma complete_chunk2827 : ∀ i : Fin 200, Compatible (565400 + i.val) →
    (table.lookup (565400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2827 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 565400 565600 :=
  FiniteIntervals.of_fin 565400 200 complete_chunk2827

lemma complete_chunk2828 : ∀ i : Fin 200, Compatible (565600 + i.val) →
    (table.lookup (565600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2828 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 565600 565800 :=
  FiniteIntervals.of_fin 565600 200 complete_chunk2828

lemma complete_chunk2829 : ∀ i : Fin 200, Compatible (565800 + i.val) →
    (table.lookup (565800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2829 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 565800 566000 :=
  FiniteIntervals.of_fin 565800 200 complete_chunk2829

#print axioms interval_chunk2820
end Erdos184Work.PureFiveFilter4
