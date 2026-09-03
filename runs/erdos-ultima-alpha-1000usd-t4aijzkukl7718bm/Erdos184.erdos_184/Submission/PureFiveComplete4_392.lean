import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3920 : ∀ i : Fin 200, Compatible (784000 + i.val) →
    (table.lookup (784000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3920 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 784000 784200 :=
  FiniteIntervals.of_fin 784000 200 complete_chunk3920

lemma complete_chunk3921 : ∀ i : Fin 200, Compatible (784200 + i.val) →
    (table.lookup (784200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3921 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 784200 784400 :=
  FiniteIntervals.of_fin 784200 200 complete_chunk3921

lemma complete_chunk3922 : ∀ i : Fin 200, Compatible (784400 + i.val) →
    (table.lookup (784400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3922 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 784400 784600 :=
  FiniteIntervals.of_fin 784400 200 complete_chunk3922

lemma complete_chunk3923 : ∀ i : Fin 200, Compatible (784600 + i.val) →
    (table.lookup (784600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3923 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 784600 784800 :=
  FiniteIntervals.of_fin 784600 200 complete_chunk3923

lemma complete_chunk3924 : ∀ i : Fin 200, Compatible (784800 + i.val) →
    (table.lookup (784800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3924 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 784800 785000 :=
  FiniteIntervals.of_fin 784800 200 complete_chunk3924

lemma complete_chunk3925 : ∀ i : Fin 200, Compatible (785000 + i.val) →
    (table.lookup (785000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3925 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 785000 785200 :=
  FiniteIntervals.of_fin 785000 200 complete_chunk3925

lemma complete_chunk3926 : ∀ i : Fin 200, Compatible (785200 + i.val) →
    (table.lookup (785200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3926 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 785200 785400 :=
  FiniteIntervals.of_fin 785200 200 complete_chunk3926

lemma complete_chunk3927 : ∀ i : Fin 200, Compatible (785400 + i.val) →
    (table.lookup (785400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3927 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 785400 785600 :=
  FiniteIntervals.of_fin 785400 200 complete_chunk3927

lemma complete_chunk3928 : ∀ i : Fin 200, Compatible (785600 + i.val) →
    (table.lookup (785600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3928 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 785600 785800 :=
  FiniteIntervals.of_fin 785600 200 complete_chunk3928

lemma complete_chunk3929 : ∀ i : Fin 200, Compatible (785800 + i.val) →
    (table.lookup (785800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3929 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 785800 786000 :=
  FiniteIntervals.of_fin 785800 200 complete_chunk3929

#print axioms interval_chunk3920
end Erdos184Work.PureFiveFilter4
