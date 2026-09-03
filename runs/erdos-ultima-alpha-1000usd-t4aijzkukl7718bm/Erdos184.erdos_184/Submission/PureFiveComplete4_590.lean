import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5900 : ∀ i : Fin 200, Compatible (1180000 + i.val) →
    (table.lookup (1180000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5900 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1180000 1180200 :=
  FiniteIntervals.of_fin 1180000 200 complete_chunk5900

lemma complete_chunk5901 : ∀ i : Fin 200, Compatible (1180200 + i.val) →
    (table.lookup (1180200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5901 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1180200 1180400 :=
  FiniteIntervals.of_fin 1180200 200 complete_chunk5901

lemma complete_chunk5902 : ∀ i : Fin 200, Compatible (1180400 + i.val) →
    (table.lookup (1180400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5902 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1180400 1180600 :=
  FiniteIntervals.of_fin 1180400 200 complete_chunk5902

lemma complete_chunk5903 : ∀ i : Fin 200, Compatible (1180600 + i.val) →
    (table.lookup (1180600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5903 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1180600 1180800 :=
  FiniteIntervals.of_fin 1180600 200 complete_chunk5903

lemma complete_chunk5904 : ∀ i : Fin 200, Compatible (1180800 + i.val) →
    (table.lookup (1180800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5904 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1180800 1181000 :=
  FiniteIntervals.of_fin 1180800 200 complete_chunk5904

lemma complete_chunk5905 : ∀ i : Fin 200, Compatible (1181000 + i.val) →
    (table.lookup (1181000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5905 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1181000 1181200 :=
  FiniteIntervals.of_fin 1181000 200 complete_chunk5905

lemma complete_chunk5906 : ∀ i : Fin 200, Compatible (1181200 + i.val) →
    (table.lookup (1181200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5906 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1181200 1181400 :=
  FiniteIntervals.of_fin 1181200 200 complete_chunk5906

lemma complete_chunk5907 : ∀ i : Fin 200, Compatible (1181400 + i.val) →
    (table.lookup (1181400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5907 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1181400 1181600 :=
  FiniteIntervals.of_fin 1181400 200 complete_chunk5907

lemma complete_chunk5908 : ∀ i : Fin 200, Compatible (1181600 + i.val) →
    (table.lookup (1181600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5908 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1181600 1181800 :=
  FiniteIntervals.of_fin 1181600 200 complete_chunk5908

lemma complete_chunk5909 : ∀ i : Fin 200, Compatible (1181800 + i.val) →
    (table.lookup (1181800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5909 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1181800 1182000 :=
  FiniteIntervals.of_fin 1181800 200 complete_chunk5909

#print axioms interval_chunk5900
end Erdos184Work.PureFiveFilter4
