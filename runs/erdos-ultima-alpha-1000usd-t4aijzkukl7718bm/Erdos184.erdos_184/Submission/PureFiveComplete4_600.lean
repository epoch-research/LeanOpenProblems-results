import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6000 : ∀ i : Fin 200, Compatible (1200000 + i.val) →
    (table.lookup (1200000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6000 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1200000 1200200 :=
  FiniteIntervals.of_fin 1200000 200 complete_chunk6000

lemma complete_chunk6001 : ∀ i : Fin 200, Compatible (1200200 + i.val) →
    (table.lookup (1200200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6001 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1200200 1200400 :=
  FiniteIntervals.of_fin 1200200 200 complete_chunk6001

lemma complete_chunk6002 : ∀ i : Fin 200, Compatible (1200400 + i.val) →
    (table.lookup (1200400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6002 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1200400 1200600 :=
  FiniteIntervals.of_fin 1200400 200 complete_chunk6002

lemma complete_chunk6003 : ∀ i : Fin 200, Compatible (1200600 + i.val) →
    (table.lookup (1200600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6003 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1200600 1200800 :=
  FiniteIntervals.of_fin 1200600 200 complete_chunk6003

lemma complete_chunk6004 : ∀ i : Fin 200, Compatible (1200800 + i.val) →
    (table.lookup (1200800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6004 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1200800 1201000 :=
  FiniteIntervals.of_fin 1200800 200 complete_chunk6004

lemma complete_chunk6005 : ∀ i : Fin 200, Compatible (1201000 + i.val) →
    (table.lookup (1201000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6005 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1201000 1201200 :=
  FiniteIntervals.of_fin 1201000 200 complete_chunk6005

lemma complete_chunk6006 : ∀ i : Fin 200, Compatible (1201200 + i.val) →
    (table.lookup (1201200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6006 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1201200 1201400 :=
  FiniteIntervals.of_fin 1201200 200 complete_chunk6006

lemma complete_chunk6007 : ∀ i : Fin 200, Compatible (1201400 + i.val) →
    (table.lookup (1201400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6007 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1201400 1201600 :=
  FiniteIntervals.of_fin 1201400 200 complete_chunk6007

lemma complete_chunk6008 : ∀ i : Fin 200, Compatible (1201600 + i.val) →
    (table.lookup (1201600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6008 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1201600 1201800 :=
  FiniteIntervals.of_fin 1201600 200 complete_chunk6008

lemma complete_chunk6009 : ∀ i : Fin 200, Compatible (1201800 + i.val) →
    (table.lookup (1201800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6009 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1201800 1202000 :=
  FiniteIntervals.of_fin 1201800 200 complete_chunk6009

#print axioms interval_chunk6000
end Erdos184Work.PureFiveFilter4
