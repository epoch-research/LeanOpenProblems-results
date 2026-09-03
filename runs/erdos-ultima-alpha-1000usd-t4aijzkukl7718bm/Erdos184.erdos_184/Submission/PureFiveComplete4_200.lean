import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2000 : ∀ i : Fin 200, Compatible (400000 + i.val) →
    (table.lookup (400000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2000 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 400000 400200 :=
  FiniteIntervals.of_fin 400000 200 complete_chunk2000

lemma complete_chunk2001 : ∀ i : Fin 200, Compatible (400200 + i.val) →
    (table.lookup (400200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2001 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 400200 400400 :=
  FiniteIntervals.of_fin 400200 200 complete_chunk2001

lemma complete_chunk2002 : ∀ i : Fin 200, Compatible (400400 + i.val) →
    (table.lookup (400400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2002 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 400400 400600 :=
  FiniteIntervals.of_fin 400400 200 complete_chunk2002

lemma complete_chunk2003 : ∀ i : Fin 200, Compatible (400600 + i.val) →
    (table.lookup (400600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2003 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 400600 400800 :=
  FiniteIntervals.of_fin 400600 200 complete_chunk2003

lemma complete_chunk2004 : ∀ i : Fin 200, Compatible (400800 + i.val) →
    (table.lookup (400800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2004 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 400800 401000 :=
  FiniteIntervals.of_fin 400800 200 complete_chunk2004

lemma complete_chunk2005 : ∀ i : Fin 200, Compatible (401000 + i.val) →
    (table.lookup (401000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2005 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 401000 401200 :=
  FiniteIntervals.of_fin 401000 200 complete_chunk2005

lemma complete_chunk2006 : ∀ i : Fin 200, Compatible (401200 + i.val) →
    (table.lookup (401200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2006 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 401200 401400 :=
  FiniteIntervals.of_fin 401200 200 complete_chunk2006

lemma complete_chunk2007 : ∀ i : Fin 200, Compatible (401400 + i.val) →
    (table.lookup (401400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2007 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 401400 401600 :=
  FiniteIntervals.of_fin 401400 200 complete_chunk2007

lemma complete_chunk2008 : ∀ i : Fin 200, Compatible (401600 + i.val) →
    (table.lookup (401600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2008 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 401600 401800 :=
  FiniteIntervals.of_fin 401600 200 complete_chunk2008

lemma complete_chunk2009 : ∀ i : Fin 200, Compatible (401800 + i.val) →
    (table.lookup (401800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2009 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 401800 402000 :=
  FiniteIntervals.of_fin 401800 200 complete_chunk2009

#print axioms interval_chunk2000
end Erdos184Work.PureFiveFilter4
