import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5990 : ∀ i : Fin 200, Compatible (1198000 + i.val) →
    (table.lookup (1198000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5990 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1198000 1198200 :=
  FiniteIntervals.of_fin 1198000 200 complete_chunk5990

lemma complete_chunk5991 : ∀ i : Fin 200, Compatible (1198200 + i.val) →
    (table.lookup (1198200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5991 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1198200 1198400 :=
  FiniteIntervals.of_fin 1198200 200 complete_chunk5991

lemma complete_chunk5992 : ∀ i : Fin 200, Compatible (1198400 + i.val) →
    (table.lookup (1198400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5992 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1198400 1198600 :=
  FiniteIntervals.of_fin 1198400 200 complete_chunk5992

lemma complete_chunk5993 : ∀ i : Fin 200, Compatible (1198600 + i.val) →
    (table.lookup (1198600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5993 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1198600 1198800 :=
  FiniteIntervals.of_fin 1198600 200 complete_chunk5993

lemma complete_chunk5994 : ∀ i : Fin 200, Compatible (1198800 + i.val) →
    (table.lookup (1198800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5994 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1198800 1199000 :=
  FiniteIntervals.of_fin 1198800 200 complete_chunk5994

lemma complete_chunk5995 : ∀ i : Fin 200, Compatible (1199000 + i.val) →
    (table.lookup (1199000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5995 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1199000 1199200 :=
  FiniteIntervals.of_fin 1199000 200 complete_chunk5995

lemma complete_chunk5996 : ∀ i : Fin 200, Compatible (1199200 + i.val) →
    (table.lookup (1199200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5996 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1199200 1199400 :=
  FiniteIntervals.of_fin 1199200 200 complete_chunk5996

lemma complete_chunk5997 : ∀ i : Fin 200, Compatible (1199400 + i.val) →
    (table.lookup (1199400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5997 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1199400 1199600 :=
  FiniteIntervals.of_fin 1199400 200 complete_chunk5997

lemma complete_chunk5998 : ∀ i : Fin 200, Compatible (1199600 + i.val) →
    (table.lookup (1199600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5998 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1199600 1199800 :=
  FiniteIntervals.of_fin 1199600 200 complete_chunk5998

lemma complete_chunk5999 : ∀ i : Fin 200, Compatible (1199800 + i.val) →
    (table.lookup (1199800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5999 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1199800 1200000 :=
  FiniteIntervals.of_fin 1199800 200 complete_chunk5999

#print axioms interval_chunk5990
end Erdos184Work.PureFiveFilter4
