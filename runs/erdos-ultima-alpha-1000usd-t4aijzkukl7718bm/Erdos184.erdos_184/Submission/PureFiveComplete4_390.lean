import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3900 : ∀ i : Fin 200, Compatible (780000 + i.val) →
    (table.lookup (780000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3900 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 780000 780200 :=
  FiniteIntervals.of_fin 780000 200 complete_chunk3900

lemma complete_chunk3901 : ∀ i : Fin 200, Compatible (780200 + i.val) →
    (table.lookup (780200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3901 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 780200 780400 :=
  FiniteIntervals.of_fin 780200 200 complete_chunk3901

lemma complete_chunk3902 : ∀ i : Fin 200, Compatible (780400 + i.val) →
    (table.lookup (780400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3902 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 780400 780600 :=
  FiniteIntervals.of_fin 780400 200 complete_chunk3902

lemma complete_chunk3903 : ∀ i : Fin 200, Compatible (780600 + i.val) →
    (table.lookup (780600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3903 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 780600 780800 :=
  FiniteIntervals.of_fin 780600 200 complete_chunk3903

lemma complete_chunk3904 : ∀ i : Fin 200, Compatible (780800 + i.val) →
    (table.lookup (780800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3904 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 780800 781000 :=
  FiniteIntervals.of_fin 780800 200 complete_chunk3904

lemma complete_chunk3905 : ∀ i : Fin 200, Compatible (781000 + i.val) →
    (table.lookup (781000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3905 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 781000 781200 :=
  FiniteIntervals.of_fin 781000 200 complete_chunk3905

lemma complete_chunk3906 : ∀ i : Fin 200, Compatible (781200 + i.val) →
    (table.lookup (781200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3906 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 781200 781400 :=
  FiniteIntervals.of_fin 781200 200 complete_chunk3906

lemma complete_chunk3907 : ∀ i : Fin 200, Compatible (781400 + i.val) →
    (table.lookup (781400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3907 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 781400 781600 :=
  FiniteIntervals.of_fin 781400 200 complete_chunk3907

lemma complete_chunk3908 : ∀ i : Fin 200, Compatible (781600 + i.val) →
    (table.lookup (781600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3908 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 781600 781800 :=
  FiniteIntervals.of_fin 781600 200 complete_chunk3908

lemma complete_chunk3909 : ∀ i : Fin 200, Compatible (781800 + i.val) →
    (table.lookup (781800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3909 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 781800 782000 :=
  FiniteIntervals.of_fin 781800 200 complete_chunk3909

#print axioms interval_chunk3900
end Erdos184Work.PureFiveFilter4
