import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2990 : ∀ i : Fin 200, Compatible (598000 + i.val) →
    (table.lookup (598000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2990 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 598000 598200 :=
  FiniteIntervals.of_fin 598000 200 complete_chunk2990

lemma complete_chunk2991 : ∀ i : Fin 200, Compatible (598200 + i.val) →
    (table.lookup (598200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2991 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 598200 598400 :=
  FiniteIntervals.of_fin 598200 200 complete_chunk2991

lemma complete_chunk2992 : ∀ i : Fin 200, Compatible (598400 + i.val) →
    (table.lookup (598400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2992 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 598400 598600 :=
  FiniteIntervals.of_fin 598400 200 complete_chunk2992

lemma complete_chunk2993 : ∀ i : Fin 200, Compatible (598600 + i.val) →
    (table.lookup (598600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2993 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 598600 598800 :=
  FiniteIntervals.of_fin 598600 200 complete_chunk2993

lemma complete_chunk2994 : ∀ i : Fin 200, Compatible (598800 + i.val) →
    (table.lookup (598800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2994 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 598800 599000 :=
  FiniteIntervals.of_fin 598800 200 complete_chunk2994

lemma complete_chunk2995 : ∀ i : Fin 200, Compatible (599000 + i.val) →
    (table.lookup (599000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2995 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 599000 599200 :=
  FiniteIntervals.of_fin 599000 200 complete_chunk2995

lemma complete_chunk2996 : ∀ i : Fin 200, Compatible (599200 + i.val) →
    (table.lookup (599200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2996 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 599200 599400 :=
  FiniteIntervals.of_fin 599200 200 complete_chunk2996

lemma complete_chunk2997 : ∀ i : Fin 200, Compatible (599400 + i.val) →
    (table.lookup (599400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2997 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 599400 599600 :=
  FiniteIntervals.of_fin 599400 200 complete_chunk2997

lemma complete_chunk2998 : ∀ i : Fin 200, Compatible (599600 + i.val) →
    (table.lookup (599600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2998 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 599600 599800 :=
  FiniteIntervals.of_fin 599600 200 complete_chunk2998

lemma complete_chunk2999 : ∀ i : Fin 200, Compatible (599800 + i.val) →
    (table.lookup (599800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2999 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 599800 600000 :=
  FiniteIntervals.of_fin 599800 200 complete_chunk2999

#print axioms interval_chunk2990
end Erdos184Work.PureFiveFilter4
