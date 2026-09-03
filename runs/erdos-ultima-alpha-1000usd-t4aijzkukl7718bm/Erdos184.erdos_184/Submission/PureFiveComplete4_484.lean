import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4840 : ∀ i : Fin 200, Compatible (968000 + i.val) →
    (table.lookup (968000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4840 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 968000 968200 :=
  FiniteIntervals.of_fin 968000 200 complete_chunk4840

lemma complete_chunk4841 : ∀ i : Fin 200, Compatible (968200 + i.val) →
    (table.lookup (968200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4841 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 968200 968400 :=
  FiniteIntervals.of_fin 968200 200 complete_chunk4841

lemma complete_chunk4842 : ∀ i : Fin 200, Compatible (968400 + i.val) →
    (table.lookup (968400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4842 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 968400 968600 :=
  FiniteIntervals.of_fin 968400 200 complete_chunk4842

lemma complete_chunk4843 : ∀ i : Fin 200, Compatible (968600 + i.val) →
    (table.lookup (968600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4843 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 968600 968800 :=
  FiniteIntervals.of_fin 968600 200 complete_chunk4843

lemma complete_chunk4844 : ∀ i : Fin 200, Compatible (968800 + i.val) →
    (table.lookup (968800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4844 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 968800 969000 :=
  FiniteIntervals.of_fin 968800 200 complete_chunk4844

lemma complete_chunk4845 : ∀ i : Fin 200, Compatible (969000 + i.val) →
    (table.lookup (969000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4845 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 969000 969200 :=
  FiniteIntervals.of_fin 969000 200 complete_chunk4845

lemma complete_chunk4846 : ∀ i : Fin 200, Compatible (969200 + i.val) →
    (table.lookup (969200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4846 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 969200 969400 :=
  FiniteIntervals.of_fin 969200 200 complete_chunk4846

lemma complete_chunk4847 : ∀ i : Fin 200, Compatible (969400 + i.val) →
    (table.lookup (969400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4847 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 969400 969600 :=
  FiniteIntervals.of_fin 969400 200 complete_chunk4847

lemma complete_chunk4848 : ∀ i : Fin 200, Compatible (969600 + i.val) →
    (table.lookup (969600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4848 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 969600 969800 :=
  FiniteIntervals.of_fin 969600 200 complete_chunk4848

lemma complete_chunk4849 : ∀ i : Fin 200, Compatible (969800 + i.val) →
    (table.lookup (969800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4849 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 969800 970000 :=
  FiniteIntervals.of_fin 969800 200 complete_chunk4849

#print axioms interval_chunk4840
end Erdos184Work.PureFiveFilter4
