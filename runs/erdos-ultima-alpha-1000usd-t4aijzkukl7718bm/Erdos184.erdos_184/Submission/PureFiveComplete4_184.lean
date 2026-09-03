import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1840 : ∀ i : Fin 200, Compatible (368000 + i.val) →
    (table.lookup (368000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1840 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 368000 368200 :=
  FiniteIntervals.of_fin 368000 200 complete_chunk1840

lemma complete_chunk1841 : ∀ i : Fin 200, Compatible (368200 + i.val) →
    (table.lookup (368200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1841 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 368200 368400 :=
  FiniteIntervals.of_fin 368200 200 complete_chunk1841

lemma complete_chunk1842 : ∀ i : Fin 200, Compatible (368400 + i.val) →
    (table.lookup (368400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1842 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 368400 368600 :=
  FiniteIntervals.of_fin 368400 200 complete_chunk1842

lemma complete_chunk1843 : ∀ i : Fin 200, Compatible (368600 + i.val) →
    (table.lookup (368600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1843 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 368600 368800 :=
  FiniteIntervals.of_fin 368600 200 complete_chunk1843

lemma complete_chunk1844 : ∀ i : Fin 200, Compatible (368800 + i.val) →
    (table.lookup (368800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1844 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 368800 369000 :=
  FiniteIntervals.of_fin 368800 200 complete_chunk1844

lemma complete_chunk1845 : ∀ i : Fin 200, Compatible (369000 + i.val) →
    (table.lookup (369000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1845 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 369000 369200 :=
  FiniteIntervals.of_fin 369000 200 complete_chunk1845

lemma complete_chunk1846 : ∀ i : Fin 200, Compatible (369200 + i.val) →
    (table.lookup (369200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1846 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 369200 369400 :=
  FiniteIntervals.of_fin 369200 200 complete_chunk1846

lemma complete_chunk1847 : ∀ i : Fin 200, Compatible (369400 + i.val) →
    (table.lookup (369400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1847 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 369400 369600 :=
  FiniteIntervals.of_fin 369400 200 complete_chunk1847

lemma complete_chunk1848 : ∀ i : Fin 200, Compatible (369600 + i.val) →
    (table.lookup (369600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1848 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 369600 369800 :=
  FiniteIntervals.of_fin 369600 200 complete_chunk1848

lemma complete_chunk1849 : ∀ i : Fin 200, Compatible (369800 + i.val) →
    (table.lookup (369800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1849 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 369800 370000 :=
  FiniteIntervals.of_fin 369800 200 complete_chunk1849

#print axioms interval_chunk1840
end Erdos184Work.PureFiveFilter4
