import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2790 : ∀ i : Fin 200, Compatible (558000 + i.val) →
    (table.lookup (558000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2790 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 558000 558200 :=
  FiniteIntervals.of_fin 558000 200 complete_chunk2790

lemma complete_chunk2791 : ∀ i : Fin 200, Compatible (558200 + i.val) →
    (table.lookup (558200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2791 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 558200 558400 :=
  FiniteIntervals.of_fin 558200 200 complete_chunk2791

lemma complete_chunk2792 : ∀ i : Fin 200, Compatible (558400 + i.val) →
    (table.lookup (558400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2792 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 558400 558600 :=
  FiniteIntervals.of_fin 558400 200 complete_chunk2792

lemma complete_chunk2793 : ∀ i : Fin 200, Compatible (558600 + i.val) →
    (table.lookup (558600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2793 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 558600 558800 :=
  FiniteIntervals.of_fin 558600 200 complete_chunk2793

lemma complete_chunk2794 : ∀ i : Fin 200, Compatible (558800 + i.val) →
    (table.lookup (558800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2794 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 558800 559000 :=
  FiniteIntervals.of_fin 558800 200 complete_chunk2794

lemma complete_chunk2795 : ∀ i : Fin 200, Compatible (559000 + i.val) →
    (table.lookup (559000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2795 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 559000 559200 :=
  FiniteIntervals.of_fin 559000 200 complete_chunk2795

lemma complete_chunk2796 : ∀ i : Fin 200, Compatible (559200 + i.val) →
    (table.lookup (559200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2796 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 559200 559400 :=
  FiniteIntervals.of_fin 559200 200 complete_chunk2796

lemma complete_chunk2797 : ∀ i : Fin 200, Compatible (559400 + i.val) →
    (table.lookup (559400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2797 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 559400 559600 :=
  FiniteIntervals.of_fin 559400 200 complete_chunk2797

lemma complete_chunk2798 : ∀ i : Fin 200, Compatible (559600 + i.val) →
    (table.lookup (559600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2798 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 559600 559800 :=
  FiniteIntervals.of_fin 559600 200 complete_chunk2798

lemma complete_chunk2799 : ∀ i : Fin 200, Compatible (559800 + i.val) →
    (table.lookup (559800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2799 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 559800 560000 :=
  FiniteIntervals.of_fin 559800 200 complete_chunk2799

#print axioms interval_chunk2790
end Erdos184Work.PureFiveFilter4
