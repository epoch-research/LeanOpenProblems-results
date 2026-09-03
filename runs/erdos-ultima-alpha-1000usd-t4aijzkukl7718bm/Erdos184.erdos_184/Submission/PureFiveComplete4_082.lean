import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk820 : ∀ i : Fin 200, Compatible (164000 + i.val) →
    (table.lookup (164000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk820 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 164000 164200 :=
  FiniteIntervals.of_fin 164000 200 complete_chunk820

lemma complete_chunk821 : ∀ i : Fin 200, Compatible (164200 + i.val) →
    (table.lookup (164200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk821 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 164200 164400 :=
  FiniteIntervals.of_fin 164200 200 complete_chunk821

lemma complete_chunk822 : ∀ i : Fin 200, Compatible (164400 + i.val) →
    (table.lookup (164400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk822 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 164400 164600 :=
  FiniteIntervals.of_fin 164400 200 complete_chunk822

lemma complete_chunk823 : ∀ i : Fin 200, Compatible (164600 + i.val) →
    (table.lookup (164600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk823 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 164600 164800 :=
  FiniteIntervals.of_fin 164600 200 complete_chunk823

lemma complete_chunk824 : ∀ i : Fin 200, Compatible (164800 + i.val) →
    (table.lookup (164800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk824 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 164800 165000 :=
  FiniteIntervals.of_fin 164800 200 complete_chunk824

lemma complete_chunk825 : ∀ i : Fin 200, Compatible (165000 + i.val) →
    (table.lookup (165000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk825 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 165000 165200 :=
  FiniteIntervals.of_fin 165000 200 complete_chunk825

lemma complete_chunk826 : ∀ i : Fin 200, Compatible (165200 + i.val) →
    (table.lookup (165200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk826 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 165200 165400 :=
  FiniteIntervals.of_fin 165200 200 complete_chunk826

lemma complete_chunk827 : ∀ i : Fin 200, Compatible (165400 + i.val) →
    (table.lookup (165400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk827 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 165400 165600 :=
  FiniteIntervals.of_fin 165400 200 complete_chunk827

lemma complete_chunk828 : ∀ i : Fin 200, Compatible (165600 + i.val) →
    (table.lookup (165600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk828 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 165600 165800 :=
  FiniteIntervals.of_fin 165600 200 complete_chunk828

lemma complete_chunk829 : ∀ i : Fin 200, Compatible (165800 + i.val) →
    (table.lookup (165800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk829 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 165800 166000 :=
  FiniteIntervals.of_fin 165800 200 complete_chunk829

#print axioms interval_chunk820
end Erdos184Work.PureFiveFilter4
