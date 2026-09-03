import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1910 : ∀ i : Fin 200, Compatible (382000 + i.val) →
    (table.lookup (382000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1910 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 382000 382200 :=
  FiniteIntervals.of_fin 382000 200 complete_chunk1910

lemma complete_chunk1911 : ∀ i : Fin 200, Compatible (382200 + i.val) →
    (table.lookup (382200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1911 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 382200 382400 :=
  FiniteIntervals.of_fin 382200 200 complete_chunk1911

lemma complete_chunk1912 : ∀ i : Fin 200, Compatible (382400 + i.val) →
    (table.lookup (382400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1912 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 382400 382600 :=
  FiniteIntervals.of_fin 382400 200 complete_chunk1912

lemma complete_chunk1913 : ∀ i : Fin 200, Compatible (382600 + i.val) →
    (table.lookup (382600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1913 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 382600 382800 :=
  FiniteIntervals.of_fin 382600 200 complete_chunk1913

lemma complete_chunk1914 : ∀ i : Fin 200, Compatible (382800 + i.val) →
    (table.lookup (382800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1914 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 382800 383000 :=
  FiniteIntervals.of_fin 382800 200 complete_chunk1914

lemma complete_chunk1915 : ∀ i : Fin 200, Compatible (383000 + i.val) →
    (table.lookup (383000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1915 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 383000 383200 :=
  FiniteIntervals.of_fin 383000 200 complete_chunk1915

lemma complete_chunk1916 : ∀ i : Fin 200, Compatible (383200 + i.val) →
    (table.lookup (383200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1916 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 383200 383400 :=
  FiniteIntervals.of_fin 383200 200 complete_chunk1916

lemma complete_chunk1917 : ∀ i : Fin 200, Compatible (383400 + i.val) →
    (table.lookup (383400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1917 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 383400 383600 :=
  FiniteIntervals.of_fin 383400 200 complete_chunk1917

lemma complete_chunk1918 : ∀ i : Fin 200, Compatible (383600 + i.val) →
    (table.lookup (383600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1918 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 383600 383800 :=
  FiniteIntervals.of_fin 383600 200 complete_chunk1918

lemma complete_chunk1919 : ∀ i : Fin 200, Compatible (383800 + i.val) →
    (table.lookup (383800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1919 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 383800 384000 :=
  FiniteIntervals.of_fin 383800 200 complete_chunk1919

#print axioms interval_chunk1910
end Erdos184Work.PureFiveFilter4
