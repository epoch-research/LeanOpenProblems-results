import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk990 : ∀ i : Fin 200, Compatible (198000 + i.val) →
    (table.lookup (198000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk990 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 198000 198200 :=
  FiniteIntervals.of_fin 198000 200 complete_chunk990

lemma complete_chunk991 : ∀ i : Fin 200, Compatible (198200 + i.val) →
    (table.lookup (198200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk991 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 198200 198400 :=
  FiniteIntervals.of_fin 198200 200 complete_chunk991

lemma complete_chunk992 : ∀ i : Fin 200, Compatible (198400 + i.val) →
    (table.lookup (198400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk992 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 198400 198600 :=
  FiniteIntervals.of_fin 198400 200 complete_chunk992

lemma complete_chunk993 : ∀ i : Fin 200, Compatible (198600 + i.val) →
    (table.lookup (198600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk993 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 198600 198800 :=
  FiniteIntervals.of_fin 198600 200 complete_chunk993

lemma complete_chunk994 : ∀ i : Fin 200, Compatible (198800 + i.val) →
    (table.lookup (198800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk994 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 198800 199000 :=
  FiniteIntervals.of_fin 198800 200 complete_chunk994

lemma complete_chunk995 : ∀ i : Fin 200, Compatible (199000 + i.val) →
    (table.lookup (199000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk995 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 199000 199200 :=
  FiniteIntervals.of_fin 199000 200 complete_chunk995

lemma complete_chunk996 : ∀ i : Fin 200, Compatible (199200 + i.val) →
    (table.lookup (199200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk996 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 199200 199400 :=
  FiniteIntervals.of_fin 199200 200 complete_chunk996

lemma complete_chunk997 : ∀ i : Fin 200, Compatible (199400 + i.val) →
    (table.lookup (199400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk997 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 199400 199600 :=
  FiniteIntervals.of_fin 199400 200 complete_chunk997

lemma complete_chunk998 : ∀ i : Fin 200, Compatible (199600 + i.val) →
    (table.lookup (199600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk998 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 199600 199800 :=
  FiniteIntervals.of_fin 199600 200 complete_chunk998

lemma complete_chunk999 : ∀ i : Fin 200, Compatible (199800 + i.val) →
    (table.lookup (199800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk999 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 199800 200000 :=
  FiniteIntervals.of_fin 199800 200 complete_chunk999

#print axioms interval_chunk990
end Erdos184Work.PureFiveFilter4
