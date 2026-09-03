import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3990 : ∀ i : Fin 200, Compatible (798000 + i.val) →
    (table.lookup (798000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3990 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 798000 798200 :=
  FiniteIntervals.of_fin 798000 200 complete_chunk3990

lemma complete_chunk3991 : ∀ i : Fin 200, Compatible (798200 + i.val) →
    (table.lookup (798200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3991 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 798200 798400 :=
  FiniteIntervals.of_fin 798200 200 complete_chunk3991

lemma complete_chunk3992 : ∀ i : Fin 200, Compatible (798400 + i.val) →
    (table.lookup (798400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3992 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 798400 798600 :=
  FiniteIntervals.of_fin 798400 200 complete_chunk3992

lemma complete_chunk3993 : ∀ i : Fin 200, Compatible (798600 + i.val) →
    (table.lookup (798600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3993 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 798600 798800 :=
  FiniteIntervals.of_fin 798600 200 complete_chunk3993

lemma complete_chunk3994 : ∀ i : Fin 200, Compatible (798800 + i.val) →
    (table.lookup (798800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3994 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 798800 799000 :=
  FiniteIntervals.of_fin 798800 200 complete_chunk3994

lemma complete_chunk3995 : ∀ i : Fin 200, Compatible (799000 + i.val) →
    (table.lookup (799000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3995 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 799000 799200 :=
  FiniteIntervals.of_fin 799000 200 complete_chunk3995

lemma complete_chunk3996 : ∀ i : Fin 200, Compatible (799200 + i.val) →
    (table.lookup (799200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3996 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 799200 799400 :=
  FiniteIntervals.of_fin 799200 200 complete_chunk3996

lemma complete_chunk3997 : ∀ i : Fin 200, Compatible (799400 + i.val) →
    (table.lookup (799400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3997 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 799400 799600 :=
  FiniteIntervals.of_fin 799400 200 complete_chunk3997

lemma complete_chunk3998 : ∀ i : Fin 200, Compatible (799600 + i.val) →
    (table.lookup (799600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3998 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 799600 799800 :=
  FiniteIntervals.of_fin 799600 200 complete_chunk3998

lemma complete_chunk3999 : ∀ i : Fin 200, Compatible (799800 + i.val) →
    (table.lookup (799800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3999 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 799800 800000 :=
  FiniteIntervals.of_fin 799800 200 complete_chunk3999

#print axioms interval_chunk3990
end Erdos184Work.PureFiveFilter4
