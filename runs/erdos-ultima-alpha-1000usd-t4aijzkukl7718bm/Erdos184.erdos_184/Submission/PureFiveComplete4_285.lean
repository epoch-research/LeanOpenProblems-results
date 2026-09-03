import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2850 : ∀ i : Fin 200, Compatible (570000 + i.val) →
    (table.lookup (570000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2850 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 570000 570200 :=
  FiniteIntervals.of_fin 570000 200 complete_chunk2850

lemma complete_chunk2851 : ∀ i : Fin 200, Compatible (570200 + i.val) →
    (table.lookup (570200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2851 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 570200 570400 :=
  FiniteIntervals.of_fin 570200 200 complete_chunk2851

lemma complete_chunk2852 : ∀ i : Fin 200, Compatible (570400 + i.val) →
    (table.lookup (570400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2852 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 570400 570600 :=
  FiniteIntervals.of_fin 570400 200 complete_chunk2852

lemma complete_chunk2853 : ∀ i : Fin 200, Compatible (570600 + i.val) →
    (table.lookup (570600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2853 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 570600 570800 :=
  FiniteIntervals.of_fin 570600 200 complete_chunk2853

lemma complete_chunk2854 : ∀ i : Fin 200, Compatible (570800 + i.val) →
    (table.lookup (570800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2854 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 570800 571000 :=
  FiniteIntervals.of_fin 570800 200 complete_chunk2854

lemma complete_chunk2855 : ∀ i : Fin 200, Compatible (571000 + i.val) →
    (table.lookup (571000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2855 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 571000 571200 :=
  FiniteIntervals.of_fin 571000 200 complete_chunk2855

lemma complete_chunk2856 : ∀ i : Fin 200, Compatible (571200 + i.val) →
    (table.lookup (571200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2856 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 571200 571400 :=
  FiniteIntervals.of_fin 571200 200 complete_chunk2856

lemma complete_chunk2857 : ∀ i : Fin 200, Compatible (571400 + i.val) →
    (table.lookup (571400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2857 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 571400 571600 :=
  FiniteIntervals.of_fin 571400 200 complete_chunk2857

lemma complete_chunk2858 : ∀ i : Fin 200, Compatible (571600 + i.val) →
    (table.lookup (571600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2858 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 571600 571800 :=
  FiniteIntervals.of_fin 571600 200 complete_chunk2858

lemma complete_chunk2859 : ∀ i : Fin 200, Compatible (571800 + i.val) →
    (table.lookup (571800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2859 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 571800 572000 :=
  FiniteIntervals.of_fin 571800 200 complete_chunk2859

#print axioms interval_chunk2850
end Erdos184Work.PureFiveFilter4
