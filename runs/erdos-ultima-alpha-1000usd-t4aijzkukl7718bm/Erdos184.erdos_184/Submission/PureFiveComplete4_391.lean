import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3910 : ∀ i : Fin 200, Compatible (782000 + i.val) →
    (table.lookup (782000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3910 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 782000 782200 :=
  FiniteIntervals.of_fin 782000 200 complete_chunk3910

lemma complete_chunk3911 : ∀ i : Fin 200, Compatible (782200 + i.val) →
    (table.lookup (782200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3911 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 782200 782400 :=
  FiniteIntervals.of_fin 782200 200 complete_chunk3911

lemma complete_chunk3912 : ∀ i : Fin 200, Compatible (782400 + i.val) →
    (table.lookup (782400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3912 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 782400 782600 :=
  FiniteIntervals.of_fin 782400 200 complete_chunk3912

lemma complete_chunk3913 : ∀ i : Fin 200, Compatible (782600 + i.val) →
    (table.lookup (782600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3913 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 782600 782800 :=
  FiniteIntervals.of_fin 782600 200 complete_chunk3913

lemma complete_chunk3914 : ∀ i : Fin 200, Compatible (782800 + i.val) →
    (table.lookup (782800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3914 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 782800 783000 :=
  FiniteIntervals.of_fin 782800 200 complete_chunk3914

lemma complete_chunk3915 : ∀ i : Fin 200, Compatible (783000 + i.val) →
    (table.lookup (783000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3915 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 783000 783200 :=
  FiniteIntervals.of_fin 783000 200 complete_chunk3915

lemma complete_chunk3916 : ∀ i : Fin 200, Compatible (783200 + i.val) →
    (table.lookup (783200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3916 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 783200 783400 :=
  FiniteIntervals.of_fin 783200 200 complete_chunk3916

lemma complete_chunk3917 : ∀ i : Fin 200, Compatible (783400 + i.val) →
    (table.lookup (783400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3917 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 783400 783600 :=
  FiniteIntervals.of_fin 783400 200 complete_chunk3917

lemma complete_chunk3918 : ∀ i : Fin 200, Compatible (783600 + i.val) →
    (table.lookup (783600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3918 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 783600 783800 :=
  FiniteIntervals.of_fin 783600 200 complete_chunk3918

lemma complete_chunk3919 : ∀ i : Fin 200, Compatible (783800 + i.val) →
    (table.lookup (783800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3919 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 783800 784000 :=
  FiniteIntervals.of_fin 783800 200 complete_chunk3919

#print axioms interval_chunk3910
end Erdos184Work.PureFiveFilter4
