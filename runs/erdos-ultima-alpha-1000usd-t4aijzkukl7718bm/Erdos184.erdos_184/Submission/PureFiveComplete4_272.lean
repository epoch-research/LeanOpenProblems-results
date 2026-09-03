import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2720 : ∀ i : Fin 200, Compatible (544000 + i.val) →
    (table.lookup (544000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2720 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 544000 544200 :=
  FiniteIntervals.of_fin 544000 200 complete_chunk2720

lemma complete_chunk2721 : ∀ i : Fin 200, Compatible (544200 + i.val) →
    (table.lookup (544200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2721 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 544200 544400 :=
  FiniteIntervals.of_fin 544200 200 complete_chunk2721

lemma complete_chunk2722 : ∀ i : Fin 200, Compatible (544400 + i.val) →
    (table.lookup (544400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2722 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 544400 544600 :=
  FiniteIntervals.of_fin 544400 200 complete_chunk2722

lemma complete_chunk2723 : ∀ i : Fin 200, Compatible (544600 + i.val) →
    (table.lookup (544600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2723 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 544600 544800 :=
  FiniteIntervals.of_fin 544600 200 complete_chunk2723

lemma complete_chunk2724 : ∀ i : Fin 200, Compatible (544800 + i.val) →
    (table.lookup (544800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2724 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 544800 545000 :=
  FiniteIntervals.of_fin 544800 200 complete_chunk2724

lemma complete_chunk2725 : ∀ i : Fin 200, Compatible (545000 + i.val) →
    (table.lookup (545000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2725 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 545000 545200 :=
  FiniteIntervals.of_fin 545000 200 complete_chunk2725

lemma complete_chunk2726 : ∀ i : Fin 200, Compatible (545200 + i.val) →
    (table.lookup (545200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2726 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 545200 545400 :=
  FiniteIntervals.of_fin 545200 200 complete_chunk2726

lemma complete_chunk2727 : ∀ i : Fin 200, Compatible (545400 + i.val) →
    (table.lookup (545400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2727 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 545400 545600 :=
  FiniteIntervals.of_fin 545400 200 complete_chunk2727

lemma complete_chunk2728 : ∀ i : Fin 200, Compatible (545600 + i.val) →
    (table.lookup (545600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2728 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 545600 545800 :=
  FiniteIntervals.of_fin 545600 200 complete_chunk2728

lemma complete_chunk2729 : ∀ i : Fin 200, Compatible (545800 + i.val) →
    (table.lookup (545800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2729 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 545800 546000 :=
  FiniteIntervals.of_fin 545800 200 complete_chunk2729

#print axioms interval_chunk2720
end Erdos184Work.PureFiveFilter4
