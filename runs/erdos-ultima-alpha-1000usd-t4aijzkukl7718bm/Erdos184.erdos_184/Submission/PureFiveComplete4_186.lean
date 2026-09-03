import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1860 : ∀ i : Fin 200, Compatible (372000 + i.val) →
    (table.lookup (372000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1860 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 372000 372200 :=
  FiniteIntervals.of_fin 372000 200 complete_chunk1860

lemma complete_chunk1861 : ∀ i : Fin 200, Compatible (372200 + i.val) →
    (table.lookup (372200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1861 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 372200 372400 :=
  FiniteIntervals.of_fin 372200 200 complete_chunk1861

lemma complete_chunk1862 : ∀ i : Fin 200, Compatible (372400 + i.val) →
    (table.lookup (372400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1862 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 372400 372600 :=
  FiniteIntervals.of_fin 372400 200 complete_chunk1862

lemma complete_chunk1863 : ∀ i : Fin 200, Compatible (372600 + i.val) →
    (table.lookup (372600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1863 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 372600 372800 :=
  FiniteIntervals.of_fin 372600 200 complete_chunk1863

lemma complete_chunk1864 : ∀ i : Fin 200, Compatible (372800 + i.val) →
    (table.lookup (372800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1864 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 372800 373000 :=
  FiniteIntervals.of_fin 372800 200 complete_chunk1864

lemma complete_chunk1865 : ∀ i : Fin 200, Compatible (373000 + i.val) →
    (table.lookup (373000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1865 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 373000 373200 :=
  FiniteIntervals.of_fin 373000 200 complete_chunk1865

lemma complete_chunk1866 : ∀ i : Fin 200, Compatible (373200 + i.val) →
    (table.lookup (373200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1866 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 373200 373400 :=
  FiniteIntervals.of_fin 373200 200 complete_chunk1866

lemma complete_chunk1867 : ∀ i : Fin 200, Compatible (373400 + i.val) →
    (table.lookup (373400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1867 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 373400 373600 :=
  FiniteIntervals.of_fin 373400 200 complete_chunk1867

lemma complete_chunk1868 : ∀ i : Fin 200, Compatible (373600 + i.val) →
    (table.lookup (373600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1868 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 373600 373800 :=
  FiniteIntervals.of_fin 373600 200 complete_chunk1868

lemma complete_chunk1869 : ∀ i : Fin 200, Compatible (373800 + i.val) →
    (table.lookup (373800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1869 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 373800 374000 :=
  FiniteIntervals.of_fin 373800 200 complete_chunk1869

#print axioms interval_chunk1860
end Erdos184Work.PureFiveFilter4
