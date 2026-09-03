import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk900 : ∀ i : Fin 200, Compatible (180000 + i.val) →
    (table.lookup (180000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk900 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 180000 180200 :=
  FiniteIntervals.of_fin 180000 200 complete_chunk900

lemma complete_chunk901 : ∀ i : Fin 200, Compatible (180200 + i.val) →
    (table.lookup (180200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk901 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 180200 180400 :=
  FiniteIntervals.of_fin 180200 200 complete_chunk901

lemma complete_chunk902 : ∀ i : Fin 200, Compatible (180400 + i.val) →
    (table.lookup (180400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk902 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 180400 180600 :=
  FiniteIntervals.of_fin 180400 200 complete_chunk902

lemma complete_chunk903 : ∀ i : Fin 200, Compatible (180600 + i.val) →
    (table.lookup (180600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk903 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 180600 180800 :=
  FiniteIntervals.of_fin 180600 200 complete_chunk903

lemma complete_chunk904 : ∀ i : Fin 200, Compatible (180800 + i.val) →
    (table.lookup (180800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk904 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 180800 181000 :=
  FiniteIntervals.of_fin 180800 200 complete_chunk904

lemma complete_chunk905 : ∀ i : Fin 200, Compatible (181000 + i.val) →
    (table.lookup (181000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk905 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 181000 181200 :=
  FiniteIntervals.of_fin 181000 200 complete_chunk905

lemma complete_chunk906 : ∀ i : Fin 200, Compatible (181200 + i.val) →
    (table.lookup (181200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk906 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 181200 181400 :=
  FiniteIntervals.of_fin 181200 200 complete_chunk906

lemma complete_chunk907 : ∀ i : Fin 200, Compatible (181400 + i.val) →
    (table.lookup (181400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk907 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 181400 181600 :=
  FiniteIntervals.of_fin 181400 200 complete_chunk907

lemma complete_chunk908 : ∀ i : Fin 200, Compatible (181600 + i.val) →
    (table.lookup (181600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk908 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 181600 181800 :=
  FiniteIntervals.of_fin 181600 200 complete_chunk908

lemma complete_chunk909 : ∀ i : Fin 200, Compatible (181800 + i.val) →
    (table.lookup (181800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk909 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 181800 182000 :=
  FiniteIntervals.of_fin 181800 200 complete_chunk909

#print axioms interval_chunk900
end Erdos184Work.PureFiveFilter4
