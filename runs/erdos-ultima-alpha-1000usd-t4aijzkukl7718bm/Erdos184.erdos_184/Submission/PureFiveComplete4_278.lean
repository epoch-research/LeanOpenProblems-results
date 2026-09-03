import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2780 : ∀ i : Fin 200, Compatible (556000 + i.val) →
    (table.lookup (556000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2780 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 556000 556200 :=
  FiniteIntervals.of_fin 556000 200 complete_chunk2780

lemma complete_chunk2781 : ∀ i : Fin 200, Compatible (556200 + i.val) →
    (table.lookup (556200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2781 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 556200 556400 :=
  FiniteIntervals.of_fin 556200 200 complete_chunk2781

lemma complete_chunk2782 : ∀ i : Fin 200, Compatible (556400 + i.val) →
    (table.lookup (556400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2782 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 556400 556600 :=
  FiniteIntervals.of_fin 556400 200 complete_chunk2782

lemma complete_chunk2783 : ∀ i : Fin 200, Compatible (556600 + i.val) →
    (table.lookup (556600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2783 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 556600 556800 :=
  FiniteIntervals.of_fin 556600 200 complete_chunk2783

lemma complete_chunk2784 : ∀ i : Fin 200, Compatible (556800 + i.val) →
    (table.lookup (556800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2784 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 556800 557000 :=
  FiniteIntervals.of_fin 556800 200 complete_chunk2784

lemma complete_chunk2785 : ∀ i : Fin 200, Compatible (557000 + i.val) →
    (table.lookup (557000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2785 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 557000 557200 :=
  FiniteIntervals.of_fin 557000 200 complete_chunk2785

lemma complete_chunk2786 : ∀ i : Fin 200, Compatible (557200 + i.val) →
    (table.lookup (557200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2786 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 557200 557400 :=
  FiniteIntervals.of_fin 557200 200 complete_chunk2786

lemma complete_chunk2787 : ∀ i : Fin 200, Compatible (557400 + i.val) →
    (table.lookup (557400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2787 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 557400 557600 :=
  FiniteIntervals.of_fin 557400 200 complete_chunk2787

lemma complete_chunk2788 : ∀ i : Fin 200, Compatible (557600 + i.val) →
    (table.lookup (557600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2788 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 557600 557800 :=
  FiniteIntervals.of_fin 557600 200 complete_chunk2788

lemma complete_chunk2789 : ∀ i : Fin 200, Compatible (557800 + i.val) →
    (table.lookup (557800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2789 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 557800 558000 :=
  FiniteIntervals.of_fin 557800 200 complete_chunk2789

#print axioms interval_chunk2780
end Erdos184Work.PureFiveFilter4
