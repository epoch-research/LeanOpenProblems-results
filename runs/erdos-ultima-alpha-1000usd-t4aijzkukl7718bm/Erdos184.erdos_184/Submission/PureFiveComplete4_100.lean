import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1000 : ∀ i : Fin 200, Compatible (200000 + i.val) →
    (table.lookup (200000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1000 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 200000 200200 :=
  FiniteIntervals.of_fin 200000 200 complete_chunk1000

lemma complete_chunk1001 : ∀ i : Fin 200, Compatible (200200 + i.val) →
    (table.lookup (200200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1001 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 200200 200400 :=
  FiniteIntervals.of_fin 200200 200 complete_chunk1001

lemma complete_chunk1002 : ∀ i : Fin 200, Compatible (200400 + i.val) →
    (table.lookup (200400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1002 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 200400 200600 :=
  FiniteIntervals.of_fin 200400 200 complete_chunk1002

lemma complete_chunk1003 : ∀ i : Fin 200, Compatible (200600 + i.val) →
    (table.lookup (200600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1003 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 200600 200800 :=
  FiniteIntervals.of_fin 200600 200 complete_chunk1003

lemma complete_chunk1004 : ∀ i : Fin 200, Compatible (200800 + i.val) →
    (table.lookup (200800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1004 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 200800 201000 :=
  FiniteIntervals.of_fin 200800 200 complete_chunk1004

lemma complete_chunk1005 : ∀ i : Fin 200, Compatible (201000 + i.val) →
    (table.lookup (201000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1005 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 201000 201200 :=
  FiniteIntervals.of_fin 201000 200 complete_chunk1005

lemma complete_chunk1006 : ∀ i : Fin 200, Compatible (201200 + i.val) →
    (table.lookup (201200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1006 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 201200 201400 :=
  FiniteIntervals.of_fin 201200 200 complete_chunk1006

lemma complete_chunk1007 : ∀ i : Fin 200, Compatible (201400 + i.val) →
    (table.lookup (201400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1007 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 201400 201600 :=
  FiniteIntervals.of_fin 201400 200 complete_chunk1007

lemma complete_chunk1008 : ∀ i : Fin 200, Compatible (201600 + i.val) →
    (table.lookup (201600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1008 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 201600 201800 :=
  FiniteIntervals.of_fin 201600 200 complete_chunk1008

lemma complete_chunk1009 : ∀ i : Fin 200, Compatible (201800 + i.val) →
    (table.lookup (201800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1009 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 201800 202000 :=
  FiniteIntervals.of_fin 201800 200 complete_chunk1009

#print axioms interval_chunk1000
end Erdos184Work.PureFiveFilter4
