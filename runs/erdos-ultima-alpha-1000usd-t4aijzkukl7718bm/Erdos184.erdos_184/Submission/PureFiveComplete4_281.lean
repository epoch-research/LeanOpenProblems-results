import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2810 : ∀ i : Fin 200, Compatible (562000 + i.val) →
    (table.lookup (562000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2810 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 562000 562200 :=
  FiniteIntervals.of_fin 562000 200 complete_chunk2810

lemma complete_chunk2811 : ∀ i : Fin 200, Compatible (562200 + i.val) →
    (table.lookup (562200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2811 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 562200 562400 :=
  FiniteIntervals.of_fin 562200 200 complete_chunk2811

lemma complete_chunk2812 : ∀ i : Fin 200, Compatible (562400 + i.val) →
    (table.lookup (562400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2812 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 562400 562600 :=
  FiniteIntervals.of_fin 562400 200 complete_chunk2812

lemma complete_chunk2813 : ∀ i : Fin 200, Compatible (562600 + i.val) →
    (table.lookup (562600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2813 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 562600 562800 :=
  FiniteIntervals.of_fin 562600 200 complete_chunk2813

lemma complete_chunk2814 : ∀ i : Fin 200, Compatible (562800 + i.val) →
    (table.lookup (562800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2814 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 562800 563000 :=
  FiniteIntervals.of_fin 562800 200 complete_chunk2814

lemma complete_chunk2815 : ∀ i : Fin 200, Compatible (563000 + i.val) →
    (table.lookup (563000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2815 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 563000 563200 :=
  FiniteIntervals.of_fin 563000 200 complete_chunk2815

lemma complete_chunk2816 : ∀ i : Fin 200, Compatible (563200 + i.val) →
    (table.lookup (563200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2816 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 563200 563400 :=
  FiniteIntervals.of_fin 563200 200 complete_chunk2816

lemma complete_chunk2817 : ∀ i : Fin 200, Compatible (563400 + i.val) →
    (table.lookup (563400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2817 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 563400 563600 :=
  FiniteIntervals.of_fin 563400 200 complete_chunk2817

lemma complete_chunk2818 : ∀ i : Fin 200, Compatible (563600 + i.val) →
    (table.lookup (563600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2818 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 563600 563800 :=
  FiniteIntervals.of_fin 563600 200 complete_chunk2818

lemma complete_chunk2819 : ∀ i : Fin 200, Compatible (563800 + i.val) →
    (table.lookup (563800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2819 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 563800 564000 :=
  FiniteIntervals.of_fin 563800 200 complete_chunk2819

#print axioms interval_chunk2810
end Erdos184Work.PureFiveFilter4
