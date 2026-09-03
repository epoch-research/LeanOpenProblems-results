import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4610 : ∀ i : Fin 200, Compatible (922000 + i.val) →
    (table.lookup (922000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4610 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 922000 922200 :=
  FiniteIntervals.of_fin 922000 200 complete_chunk4610

lemma complete_chunk4611 : ∀ i : Fin 200, Compatible (922200 + i.val) →
    (table.lookup (922200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4611 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 922200 922400 :=
  FiniteIntervals.of_fin 922200 200 complete_chunk4611

lemma complete_chunk4612 : ∀ i : Fin 200, Compatible (922400 + i.val) →
    (table.lookup (922400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4612 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 922400 922600 :=
  FiniteIntervals.of_fin 922400 200 complete_chunk4612

lemma complete_chunk4613 : ∀ i : Fin 200, Compatible (922600 + i.val) →
    (table.lookup (922600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4613 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 922600 922800 :=
  FiniteIntervals.of_fin 922600 200 complete_chunk4613

lemma complete_chunk4614 : ∀ i : Fin 200, Compatible (922800 + i.val) →
    (table.lookup (922800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4614 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 922800 923000 :=
  FiniteIntervals.of_fin 922800 200 complete_chunk4614

lemma complete_chunk4615 : ∀ i : Fin 200, Compatible (923000 + i.val) →
    (table.lookup (923000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4615 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 923000 923200 :=
  FiniteIntervals.of_fin 923000 200 complete_chunk4615

lemma complete_chunk4616 : ∀ i : Fin 200, Compatible (923200 + i.val) →
    (table.lookup (923200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4616 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 923200 923400 :=
  FiniteIntervals.of_fin 923200 200 complete_chunk4616

lemma complete_chunk4617 : ∀ i : Fin 200, Compatible (923400 + i.val) →
    (table.lookup (923400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4617 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 923400 923600 :=
  FiniteIntervals.of_fin 923400 200 complete_chunk4617

lemma complete_chunk4618 : ∀ i : Fin 200, Compatible (923600 + i.val) →
    (table.lookup (923600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4618 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 923600 923800 :=
  FiniteIntervals.of_fin 923600 200 complete_chunk4618

lemma complete_chunk4619 : ∀ i : Fin 200, Compatible (923800 + i.val) →
    (table.lookup (923800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4619 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 923800 924000 :=
  FiniteIntervals.of_fin 923800 200 complete_chunk4619

#print axioms interval_chunk4610
end Erdos184Work.PureFiveFilter4
