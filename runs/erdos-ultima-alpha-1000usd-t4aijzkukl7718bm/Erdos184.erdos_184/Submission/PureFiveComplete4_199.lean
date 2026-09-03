import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1990 : ∀ i : Fin 200, Compatible (398000 + i.val) →
    (table.lookup (398000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1990 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 398000 398200 :=
  FiniteIntervals.of_fin 398000 200 complete_chunk1990

lemma complete_chunk1991 : ∀ i : Fin 200, Compatible (398200 + i.val) →
    (table.lookup (398200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1991 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 398200 398400 :=
  FiniteIntervals.of_fin 398200 200 complete_chunk1991

lemma complete_chunk1992 : ∀ i : Fin 200, Compatible (398400 + i.val) →
    (table.lookup (398400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1992 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 398400 398600 :=
  FiniteIntervals.of_fin 398400 200 complete_chunk1992

lemma complete_chunk1993 : ∀ i : Fin 200, Compatible (398600 + i.val) →
    (table.lookup (398600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1993 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 398600 398800 :=
  FiniteIntervals.of_fin 398600 200 complete_chunk1993

lemma complete_chunk1994 : ∀ i : Fin 200, Compatible (398800 + i.val) →
    (table.lookup (398800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1994 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 398800 399000 :=
  FiniteIntervals.of_fin 398800 200 complete_chunk1994

lemma complete_chunk1995 : ∀ i : Fin 200, Compatible (399000 + i.val) →
    (table.lookup (399000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1995 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 399000 399200 :=
  FiniteIntervals.of_fin 399000 200 complete_chunk1995

lemma complete_chunk1996 : ∀ i : Fin 200, Compatible (399200 + i.val) →
    (table.lookup (399200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1996 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 399200 399400 :=
  FiniteIntervals.of_fin 399200 200 complete_chunk1996

lemma complete_chunk1997 : ∀ i : Fin 200, Compatible (399400 + i.val) →
    (table.lookup (399400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1997 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 399400 399600 :=
  FiniteIntervals.of_fin 399400 200 complete_chunk1997

lemma complete_chunk1998 : ∀ i : Fin 200, Compatible (399600 + i.val) →
    (table.lookup (399600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1998 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 399600 399800 :=
  FiniteIntervals.of_fin 399600 200 complete_chunk1998

lemma complete_chunk1999 : ∀ i : Fin 200, Compatible (399800 + i.val) →
    (table.lookup (399800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1999 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 399800 400000 :=
  FiniteIntervals.of_fin 399800 200 complete_chunk1999

#print axioms interval_chunk1990
end Erdos184Work.PureFiveFilter4
