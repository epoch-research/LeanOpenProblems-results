import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk890 : ∀ i : Fin 200, Compatible (178000 + i.val) →
    (table.lookup (178000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk890 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 178000 178200 :=
  FiniteIntervals.of_fin 178000 200 complete_chunk890

lemma complete_chunk891 : ∀ i : Fin 200, Compatible (178200 + i.val) →
    (table.lookup (178200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk891 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 178200 178400 :=
  FiniteIntervals.of_fin 178200 200 complete_chunk891

lemma complete_chunk892 : ∀ i : Fin 200, Compatible (178400 + i.val) →
    (table.lookup (178400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk892 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 178400 178600 :=
  FiniteIntervals.of_fin 178400 200 complete_chunk892

lemma complete_chunk893 : ∀ i : Fin 200, Compatible (178600 + i.val) →
    (table.lookup (178600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk893 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 178600 178800 :=
  FiniteIntervals.of_fin 178600 200 complete_chunk893

lemma complete_chunk894 : ∀ i : Fin 200, Compatible (178800 + i.val) →
    (table.lookup (178800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk894 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 178800 179000 :=
  FiniteIntervals.of_fin 178800 200 complete_chunk894

lemma complete_chunk895 : ∀ i : Fin 200, Compatible (179000 + i.val) →
    (table.lookup (179000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk895 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 179000 179200 :=
  FiniteIntervals.of_fin 179000 200 complete_chunk895

lemma complete_chunk896 : ∀ i : Fin 200, Compatible (179200 + i.val) →
    (table.lookup (179200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk896 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 179200 179400 :=
  FiniteIntervals.of_fin 179200 200 complete_chunk896

lemma complete_chunk897 : ∀ i : Fin 200, Compatible (179400 + i.val) →
    (table.lookup (179400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk897 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 179400 179600 :=
  FiniteIntervals.of_fin 179400 200 complete_chunk897

lemma complete_chunk898 : ∀ i : Fin 200, Compatible (179600 + i.val) →
    (table.lookup (179600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk898 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 179600 179800 :=
  FiniteIntervals.of_fin 179600 200 complete_chunk898

lemma complete_chunk899 : ∀ i : Fin 200, Compatible (179800 + i.val) →
    (table.lookup (179800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk899 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 179800 180000 :=
  FiniteIntervals.of_fin 179800 200 complete_chunk899

#print axioms interval_chunk890
end Erdos184Work.PureFiveFilter4
