import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1810 : ∀ i : Fin 200, Compatible (362000 + i.val) →
    (table.lookup (362000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1810 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 362000 362200 :=
  FiniteIntervals.of_fin 362000 200 complete_chunk1810

lemma complete_chunk1811 : ∀ i : Fin 200, Compatible (362200 + i.val) →
    (table.lookup (362200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1811 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 362200 362400 :=
  FiniteIntervals.of_fin 362200 200 complete_chunk1811

lemma complete_chunk1812 : ∀ i : Fin 200, Compatible (362400 + i.val) →
    (table.lookup (362400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1812 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 362400 362600 :=
  FiniteIntervals.of_fin 362400 200 complete_chunk1812

lemma complete_chunk1813 : ∀ i : Fin 200, Compatible (362600 + i.val) →
    (table.lookup (362600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1813 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 362600 362800 :=
  FiniteIntervals.of_fin 362600 200 complete_chunk1813

lemma complete_chunk1814 : ∀ i : Fin 200, Compatible (362800 + i.val) →
    (table.lookup (362800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1814 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 362800 363000 :=
  FiniteIntervals.of_fin 362800 200 complete_chunk1814

lemma complete_chunk1815 : ∀ i : Fin 200, Compatible (363000 + i.val) →
    (table.lookup (363000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1815 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 363000 363200 :=
  FiniteIntervals.of_fin 363000 200 complete_chunk1815

lemma complete_chunk1816 : ∀ i : Fin 200, Compatible (363200 + i.val) →
    (table.lookup (363200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1816 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 363200 363400 :=
  FiniteIntervals.of_fin 363200 200 complete_chunk1816

lemma complete_chunk1817 : ∀ i : Fin 200, Compatible (363400 + i.val) →
    (table.lookup (363400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1817 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 363400 363600 :=
  FiniteIntervals.of_fin 363400 200 complete_chunk1817

lemma complete_chunk1818 : ∀ i : Fin 200, Compatible (363600 + i.val) →
    (table.lookup (363600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1818 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 363600 363800 :=
  FiniteIntervals.of_fin 363600 200 complete_chunk1818

lemma complete_chunk1819 : ∀ i : Fin 200, Compatible (363800 + i.val) →
    (table.lookup (363800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1819 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 363800 364000 :=
  FiniteIntervals.of_fin 363800 200 complete_chunk1819

#print axioms interval_chunk1810
end Erdos184Work.PureFiveFilter4
