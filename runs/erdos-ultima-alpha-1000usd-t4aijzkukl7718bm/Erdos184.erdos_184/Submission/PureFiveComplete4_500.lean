import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5000 : ∀ i : Fin 200, Compatible (1000000 + i.val) →
    (table.lookup (1000000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5000 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1000000 1000200 :=
  FiniteIntervals.of_fin 1000000 200 complete_chunk5000

lemma complete_chunk5001 : ∀ i : Fin 200, Compatible (1000200 + i.val) →
    (table.lookup (1000200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5001 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1000200 1000400 :=
  FiniteIntervals.of_fin 1000200 200 complete_chunk5001

lemma complete_chunk5002 : ∀ i : Fin 200, Compatible (1000400 + i.val) →
    (table.lookup (1000400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5002 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1000400 1000600 :=
  FiniteIntervals.of_fin 1000400 200 complete_chunk5002

lemma complete_chunk5003 : ∀ i : Fin 200, Compatible (1000600 + i.val) →
    (table.lookup (1000600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5003 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1000600 1000800 :=
  FiniteIntervals.of_fin 1000600 200 complete_chunk5003

lemma complete_chunk5004 : ∀ i : Fin 200, Compatible (1000800 + i.val) →
    (table.lookup (1000800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5004 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1000800 1001000 :=
  FiniteIntervals.of_fin 1000800 200 complete_chunk5004

lemma complete_chunk5005 : ∀ i : Fin 200, Compatible (1001000 + i.val) →
    (table.lookup (1001000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5005 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1001000 1001200 :=
  FiniteIntervals.of_fin 1001000 200 complete_chunk5005

lemma complete_chunk5006 : ∀ i : Fin 200, Compatible (1001200 + i.val) →
    (table.lookup (1001200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5006 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1001200 1001400 :=
  FiniteIntervals.of_fin 1001200 200 complete_chunk5006

lemma complete_chunk5007 : ∀ i : Fin 200, Compatible (1001400 + i.val) →
    (table.lookup (1001400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5007 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1001400 1001600 :=
  FiniteIntervals.of_fin 1001400 200 complete_chunk5007

lemma complete_chunk5008 : ∀ i : Fin 200, Compatible (1001600 + i.val) →
    (table.lookup (1001600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5008 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1001600 1001800 :=
  FiniteIntervals.of_fin 1001600 200 complete_chunk5008

lemma complete_chunk5009 : ∀ i : Fin 200, Compatible (1001800 + i.val) →
    (table.lookup (1001800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5009 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1001800 1002000 :=
  FiniteIntervals.of_fin 1001800 200 complete_chunk5009

#print axioms interval_chunk5000
end Erdos184Work.PureFiveFilter4
