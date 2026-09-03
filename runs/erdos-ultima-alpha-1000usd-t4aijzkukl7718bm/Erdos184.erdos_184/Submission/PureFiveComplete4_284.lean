import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2840 : ∀ i : Fin 200, Compatible (568000 + i.val) →
    (table.lookup (568000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2840 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 568000 568200 :=
  FiniteIntervals.of_fin 568000 200 complete_chunk2840

lemma complete_chunk2841 : ∀ i : Fin 200, Compatible (568200 + i.val) →
    (table.lookup (568200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2841 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 568200 568400 :=
  FiniteIntervals.of_fin 568200 200 complete_chunk2841

lemma complete_chunk2842 : ∀ i : Fin 200, Compatible (568400 + i.val) →
    (table.lookup (568400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2842 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 568400 568600 :=
  FiniteIntervals.of_fin 568400 200 complete_chunk2842

lemma complete_chunk2843 : ∀ i : Fin 200, Compatible (568600 + i.val) →
    (table.lookup (568600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2843 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 568600 568800 :=
  FiniteIntervals.of_fin 568600 200 complete_chunk2843

lemma complete_chunk2844 : ∀ i : Fin 200, Compatible (568800 + i.val) →
    (table.lookup (568800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2844 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 568800 569000 :=
  FiniteIntervals.of_fin 568800 200 complete_chunk2844

lemma complete_chunk2845 : ∀ i : Fin 200, Compatible (569000 + i.val) →
    (table.lookup (569000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2845 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 569000 569200 :=
  FiniteIntervals.of_fin 569000 200 complete_chunk2845

lemma complete_chunk2846 : ∀ i : Fin 200, Compatible (569200 + i.val) →
    (table.lookup (569200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2846 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 569200 569400 :=
  FiniteIntervals.of_fin 569200 200 complete_chunk2846

lemma complete_chunk2847 : ∀ i : Fin 200, Compatible (569400 + i.val) →
    (table.lookup (569400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2847 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 569400 569600 :=
  FiniteIntervals.of_fin 569400 200 complete_chunk2847

lemma complete_chunk2848 : ∀ i : Fin 200, Compatible (569600 + i.val) →
    (table.lookup (569600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2848 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 569600 569800 :=
  FiniteIntervals.of_fin 569600 200 complete_chunk2848

lemma complete_chunk2849 : ∀ i : Fin 200, Compatible (569800 + i.val) →
    (table.lookup (569800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2849 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 569800 570000 :=
  FiniteIntervals.of_fin 569800 200 complete_chunk2849

#print axioms interval_chunk2840
end Erdos184Work.PureFiveFilter4
