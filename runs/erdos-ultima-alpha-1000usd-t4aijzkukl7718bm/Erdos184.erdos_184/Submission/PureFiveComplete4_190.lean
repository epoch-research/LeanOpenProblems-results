import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1900 : ∀ i : Fin 200, Compatible (380000 + i.val) →
    (table.lookup (380000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1900 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 380000 380200 :=
  FiniteIntervals.of_fin 380000 200 complete_chunk1900

lemma complete_chunk1901 : ∀ i : Fin 200, Compatible (380200 + i.val) →
    (table.lookup (380200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1901 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 380200 380400 :=
  FiniteIntervals.of_fin 380200 200 complete_chunk1901

lemma complete_chunk1902 : ∀ i : Fin 200, Compatible (380400 + i.val) →
    (table.lookup (380400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1902 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 380400 380600 :=
  FiniteIntervals.of_fin 380400 200 complete_chunk1902

lemma complete_chunk1903 : ∀ i : Fin 200, Compatible (380600 + i.val) →
    (table.lookup (380600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1903 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 380600 380800 :=
  FiniteIntervals.of_fin 380600 200 complete_chunk1903

lemma complete_chunk1904 : ∀ i : Fin 200, Compatible (380800 + i.val) →
    (table.lookup (380800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1904 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 380800 381000 :=
  FiniteIntervals.of_fin 380800 200 complete_chunk1904

lemma complete_chunk1905 : ∀ i : Fin 200, Compatible (381000 + i.val) →
    (table.lookup (381000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1905 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 381000 381200 :=
  FiniteIntervals.of_fin 381000 200 complete_chunk1905

lemma complete_chunk1906 : ∀ i : Fin 200, Compatible (381200 + i.val) →
    (table.lookup (381200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1906 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 381200 381400 :=
  FiniteIntervals.of_fin 381200 200 complete_chunk1906

lemma complete_chunk1907 : ∀ i : Fin 200, Compatible (381400 + i.val) →
    (table.lookup (381400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1907 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 381400 381600 :=
  FiniteIntervals.of_fin 381400 200 complete_chunk1907

lemma complete_chunk1908 : ∀ i : Fin 200, Compatible (381600 + i.val) →
    (table.lookup (381600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1908 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 381600 381800 :=
  FiniteIntervals.of_fin 381600 200 complete_chunk1908

lemma complete_chunk1909 : ∀ i : Fin 200, Compatible (381800 + i.val) →
    (table.lookup (381800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1909 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 381800 382000 :=
  FiniteIntervals.of_fin 381800 200 complete_chunk1909

#print axioms interval_chunk1900
end Erdos184Work.PureFiveFilter4
