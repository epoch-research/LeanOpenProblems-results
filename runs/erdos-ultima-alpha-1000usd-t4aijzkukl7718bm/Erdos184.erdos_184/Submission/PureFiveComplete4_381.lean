import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3810 : ∀ i : Fin 200, Compatible (762000 + i.val) →
    (table.lookup (762000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3810 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 762000 762200 :=
  FiniteIntervals.of_fin 762000 200 complete_chunk3810

lemma complete_chunk3811 : ∀ i : Fin 200, Compatible (762200 + i.val) →
    (table.lookup (762200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3811 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 762200 762400 :=
  FiniteIntervals.of_fin 762200 200 complete_chunk3811

lemma complete_chunk3812 : ∀ i : Fin 200, Compatible (762400 + i.val) →
    (table.lookup (762400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3812 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 762400 762600 :=
  FiniteIntervals.of_fin 762400 200 complete_chunk3812

lemma complete_chunk3813 : ∀ i : Fin 200, Compatible (762600 + i.val) →
    (table.lookup (762600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3813 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 762600 762800 :=
  FiniteIntervals.of_fin 762600 200 complete_chunk3813

lemma complete_chunk3814 : ∀ i : Fin 200, Compatible (762800 + i.val) →
    (table.lookup (762800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3814 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 762800 763000 :=
  FiniteIntervals.of_fin 762800 200 complete_chunk3814

lemma complete_chunk3815 : ∀ i : Fin 200, Compatible (763000 + i.val) →
    (table.lookup (763000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3815 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 763000 763200 :=
  FiniteIntervals.of_fin 763000 200 complete_chunk3815

lemma complete_chunk3816 : ∀ i : Fin 200, Compatible (763200 + i.val) →
    (table.lookup (763200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3816 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 763200 763400 :=
  FiniteIntervals.of_fin 763200 200 complete_chunk3816

lemma complete_chunk3817 : ∀ i : Fin 200, Compatible (763400 + i.val) →
    (table.lookup (763400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3817 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 763400 763600 :=
  FiniteIntervals.of_fin 763400 200 complete_chunk3817

lemma complete_chunk3818 : ∀ i : Fin 200, Compatible (763600 + i.val) →
    (table.lookup (763600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3818 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 763600 763800 :=
  FiniteIntervals.of_fin 763600 200 complete_chunk3818

lemma complete_chunk3819 : ∀ i : Fin 200, Compatible (763800 + i.val) →
    (table.lookup (763800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3819 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 763800 764000 :=
  FiniteIntervals.of_fin 763800 200 complete_chunk3819

#print axioms interval_chunk3810
end Erdos184Work.PureFiveFilter4
