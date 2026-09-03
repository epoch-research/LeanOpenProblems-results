import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5890 : ∀ i : Fin 200, Compatible (1178000 + i.val) →
    (table.lookup (1178000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5890 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1178000 1178200 :=
  FiniteIntervals.of_fin 1178000 200 complete_chunk5890

lemma complete_chunk5891 : ∀ i : Fin 200, Compatible (1178200 + i.val) →
    (table.lookup (1178200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5891 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1178200 1178400 :=
  FiniteIntervals.of_fin 1178200 200 complete_chunk5891

lemma complete_chunk5892 : ∀ i : Fin 200, Compatible (1178400 + i.val) →
    (table.lookup (1178400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5892 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1178400 1178600 :=
  FiniteIntervals.of_fin 1178400 200 complete_chunk5892

lemma complete_chunk5893 : ∀ i : Fin 200, Compatible (1178600 + i.val) →
    (table.lookup (1178600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5893 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1178600 1178800 :=
  FiniteIntervals.of_fin 1178600 200 complete_chunk5893

lemma complete_chunk5894 : ∀ i : Fin 200, Compatible (1178800 + i.val) →
    (table.lookup (1178800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5894 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1178800 1179000 :=
  FiniteIntervals.of_fin 1178800 200 complete_chunk5894

lemma complete_chunk5895 : ∀ i : Fin 200, Compatible (1179000 + i.val) →
    (table.lookup (1179000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5895 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1179000 1179200 :=
  FiniteIntervals.of_fin 1179000 200 complete_chunk5895

lemma complete_chunk5896 : ∀ i : Fin 200, Compatible (1179200 + i.val) →
    (table.lookup (1179200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5896 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1179200 1179400 :=
  FiniteIntervals.of_fin 1179200 200 complete_chunk5896

lemma complete_chunk5897 : ∀ i : Fin 200, Compatible (1179400 + i.val) →
    (table.lookup (1179400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5897 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1179400 1179600 :=
  FiniteIntervals.of_fin 1179400 200 complete_chunk5897

lemma complete_chunk5898 : ∀ i : Fin 200, Compatible (1179600 + i.val) →
    (table.lookup (1179600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5898 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1179600 1179800 :=
  FiniteIntervals.of_fin 1179600 200 complete_chunk5898

lemma complete_chunk5899 : ∀ i : Fin 200, Compatible (1179800 + i.val) →
    (table.lookup (1179800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5899 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1179800 1180000 :=
  FiniteIntervals.of_fin 1179800 200 complete_chunk5899

#print axioms interval_chunk5890
end Erdos184Work.PureFiveFilter4
