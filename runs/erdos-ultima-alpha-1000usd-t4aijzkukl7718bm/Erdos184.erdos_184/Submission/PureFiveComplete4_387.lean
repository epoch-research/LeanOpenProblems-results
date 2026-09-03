import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3870 : ∀ i : Fin 200, Compatible (774000 + i.val) →
    (table.lookup (774000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3870 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 774000 774200 :=
  FiniteIntervals.of_fin 774000 200 complete_chunk3870

lemma complete_chunk3871 : ∀ i : Fin 200, Compatible (774200 + i.val) →
    (table.lookup (774200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3871 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 774200 774400 :=
  FiniteIntervals.of_fin 774200 200 complete_chunk3871

lemma complete_chunk3872 : ∀ i : Fin 200, Compatible (774400 + i.val) →
    (table.lookup (774400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3872 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 774400 774600 :=
  FiniteIntervals.of_fin 774400 200 complete_chunk3872

lemma complete_chunk3873 : ∀ i : Fin 200, Compatible (774600 + i.val) →
    (table.lookup (774600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3873 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 774600 774800 :=
  FiniteIntervals.of_fin 774600 200 complete_chunk3873

lemma complete_chunk3874 : ∀ i : Fin 200, Compatible (774800 + i.val) →
    (table.lookup (774800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3874 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 774800 775000 :=
  FiniteIntervals.of_fin 774800 200 complete_chunk3874

lemma complete_chunk3875 : ∀ i : Fin 200, Compatible (775000 + i.val) →
    (table.lookup (775000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3875 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 775000 775200 :=
  FiniteIntervals.of_fin 775000 200 complete_chunk3875

lemma complete_chunk3876 : ∀ i : Fin 200, Compatible (775200 + i.val) →
    (table.lookup (775200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3876 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 775200 775400 :=
  FiniteIntervals.of_fin 775200 200 complete_chunk3876

lemma complete_chunk3877 : ∀ i : Fin 200, Compatible (775400 + i.val) →
    (table.lookup (775400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3877 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 775400 775600 :=
  FiniteIntervals.of_fin 775400 200 complete_chunk3877

lemma complete_chunk3878 : ∀ i : Fin 200, Compatible (775600 + i.val) →
    (table.lookup (775600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3878 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 775600 775800 :=
  FiniteIntervals.of_fin 775600 200 complete_chunk3878

lemma complete_chunk3879 : ∀ i : Fin 200, Compatible (775800 + i.val) →
    (table.lookup (775800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3879 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 775800 776000 :=
  FiniteIntervals.of_fin 775800 200 complete_chunk3879

#print axioms interval_chunk3870
end Erdos184Work.PureFiveFilter4
