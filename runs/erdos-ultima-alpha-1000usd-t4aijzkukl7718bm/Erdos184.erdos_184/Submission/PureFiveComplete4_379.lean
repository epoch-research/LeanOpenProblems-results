import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3790 : ∀ i : Fin 200, Compatible (758000 + i.val) →
    (table.lookup (758000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3790 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 758000 758200 :=
  FiniteIntervals.of_fin 758000 200 complete_chunk3790

lemma complete_chunk3791 : ∀ i : Fin 200, Compatible (758200 + i.val) →
    (table.lookup (758200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3791 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 758200 758400 :=
  FiniteIntervals.of_fin 758200 200 complete_chunk3791

lemma complete_chunk3792 : ∀ i : Fin 200, Compatible (758400 + i.val) →
    (table.lookup (758400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3792 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 758400 758600 :=
  FiniteIntervals.of_fin 758400 200 complete_chunk3792

lemma complete_chunk3793 : ∀ i : Fin 200, Compatible (758600 + i.val) →
    (table.lookup (758600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3793 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 758600 758800 :=
  FiniteIntervals.of_fin 758600 200 complete_chunk3793

lemma complete_chunk3794 : ∀ i : Fin 200, Compatible (758800 + i.val) →
    (table.lookup (758800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3794 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 758800 759000 :=
  FiniteIntervals.of_fin 758800 200 complete_chunk3794

lemma complete_chunk3795 : ∀ i : Fin 200, Compatible (759000 + i.val) →
    (table.lookup (759000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3795 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 759000 759200 :=
  FiniteIntervals.of_fin 759000 200 complete_chunk3795

lemma complete_chunk3796 : ∀ i : Fin 200, Compatible (759200 + i.val) →
    (table.lookup (759200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3796 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 759200 759400 :=
  FiniteIntervals.of_fin 759200 200 complete_chunk3796

lemma complete_chunk3797 : ∀ i : Fin 200, Compatible (759400 + i.val) →
    (table.lookup (759400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3797 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 759400 759600 :=
  FiniteIntervals.of_fin 759400 200 complete_chunk3797

lemma complete_chunk3798 : ∀ i : Fin 200, Compatible (759600 + i.val) →
    (table.lookup (759600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3798 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 759600 759800 :=
  FiniteIntervals.of_fin 759600 200 complete_chunk3798

lemma complete_chunk3799 : ∀ i : Fin 200, Compatible (759800 + i.val) →
    (table.lookup (759800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3799 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 759800 760000 :=
  FiniteIntervals.of_fin 759800 200 complete_chunk3799

#print axioms interval_chunk3790
end Erdos184Work.PureFiveFilter4
