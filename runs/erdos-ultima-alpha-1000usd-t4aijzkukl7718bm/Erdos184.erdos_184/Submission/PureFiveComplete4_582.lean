import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5820 : ∀ i : Fin 200, Compatible (1164000 + i.val) →
    (table.lookup (1164000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5820 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1164000 1164200 :=
  FiniteIntervals.of_fin 1164000 200 complete_chunk5820

lemma complete_chunk5821 : ∀ i : Fin 200, Compatible (1164200 + i.val) →
    (table.lookup (1164200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5821 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1164200 1164400 :=
  FiniteIntervals.of_fin 1164200 200 complete_chunk5821

lemma complete_chunk5822 : ∀ i : Fin 200, Compatible (1164400 + i.val) →
    (table.lookup (1164400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5822 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1164400 1164600 :=
  FiniteIntervals.of_fin 1164400 200 complete_chunk5822

lemma complete_chunk5823 : ∀ i : Fin 200, Compatible (1164600 + i.val) →
    (table.lookup (1164600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5823 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1164600 1164800 :=
  FiniteIntervals.of_fin 1164600 200 complete_chunk5823

lemma complete_chunk5824 : ∀ i : Fin 200, Compatible (1164800 + i.val) →
    (table.lookup (1164800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5824 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1164800 1165000 :=
  FiniteIntervals.of_fin 1164800 200 complete_chunk5824

lemma complete_chunk5825 : ∀ i : Fin 200, Compatible (1165000 + i.val) →
    (table.lookup (1165000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5825 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1165000 1165200 :=
  FiniteIntervals.of_fin 1165000 200 complete_chunk5825

lemma complete_chunk5826 : ∀ i : Fin 200, Compatible (1165200 + i.val) →
    (table.lookup (1165200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5826 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1165200 1165400 :=
  FiniteIntervals.of_fin 1165200 200 complete_chunk5826

lemma complete_chunk5827 : ∀ i : Fin 200, Compatible (1165400 + i.val) →
    (table.lookup (1165400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5827 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1165400 1165600 :=
  FiniteIntervals.of_fin 1165400 200 complete_chunk5827

lemma complete_chunk5828 : ∀ i : Fin 200, Compatible (1165600 + i.val) →
    (table.lookup (1165600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5828 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1165600 1165800 :=
  FiniteIntervals.of_fin 1165600 200 complete_chunk5828

lemma complete_chunk5829 : ∀ i : Fin 200, Compatible (1165800 + i.val) →
    (table.lookup (1165800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5829 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1165800 1166000 :=
  FiniteIntervals.of_fin 1165800 200 complete_chunk5829

#print axioms interval_chunk5820
end Erdos184Work.PureFiveFilter4
