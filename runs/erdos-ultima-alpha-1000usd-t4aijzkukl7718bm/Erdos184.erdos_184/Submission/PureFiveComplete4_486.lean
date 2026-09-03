import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4860 : ∀ i : Fin 200, Compatible (972000 + i.val) →
    (table.lookup (972000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4860 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 972000 972200 :=
  FiniteIntervals.of_fin 972000 200 complete_chunk4860

lemma complete_chunk4861 : ∀ i : Fin 200, Compatible (972200 + i.val) →
    (table.lookup (972200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4861 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 972200 972400 :=
  FiniteIntervals.of_fin 972200 200 complete_chunk4861

lemma complete_chunk4862 : ∀ i : Fin 200, Compatible (972400 + i.val) →
    (table.lookup (972400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4862 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 972400 972600 :=
  FiniteIntervals.of_fin 972400 200 complete_chunk4862

lemma complete_chunk4863 : ∀ i : Fin 200, Compatible (972600 + i.val) →
    (table.lookup (972600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4863 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 972600 972800 :=
  FiniteIntervals.of_fin 972600 200 complete_chunk4863

lemma complete_chunk4864 : ∀ i : Fin 200, Compatible (972800 + i.val) →
    (table.lookup (972800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4864 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 972800 973000 :=
  FiniteIntervals.of_fin 972800 200 complete_chunk4864

lemma complete_chunk4865 : ∀ i : Fin 200, Compatible (973000 + i.val) →
    (table.lookup (973000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4865 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 973000 973200 :=
  FiniteIntervals.of_fin 973000 200 complete_chunk4865

lemma complete_chunk4866 : ∀ i : Fin 200, Compatible (973200 + i.val) →
    (table.lookup (973200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4866 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 973200 973400 :=
  FiniteIntervals.of_fin 973200 200 complete_chunk4866

lemma complete_chunk4867 : ∀ i : Fin 200, Compatible (973400 + i.val) →
    (table.lookup (973400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4867 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 973400 973600 :=
  FiniteIntervals.of_fin 973400 200 complete_chunk4867

lemma complete_chunk4868 : ∀ i : Fin 200, Compatible (973600 + i.val) →
    (table.lookup (973600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4868 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 973600 973800 :=
  FiniteIntervals.of_fin 973600 200 complete_chunk4868

lemma complete_chunk4869 : ∀ i : Fin 200, Compatible (973800 + i.val) →
    (table.lookup (973800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4869 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 973800 974000 :=
  FiniteIntervals.of_fin 973800 200 complete_chunk4869

#print axioms interval_chunk4860
end Erdos184Work.PureFiveFilter4
