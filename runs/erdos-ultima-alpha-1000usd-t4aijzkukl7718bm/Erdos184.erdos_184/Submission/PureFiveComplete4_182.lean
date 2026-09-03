import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1820 : ∀ i : Fin 200, Compatible (364000 + i.val) →
    (table.lookup (364000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1820 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 364000 364200 :=
  FiniteIntervals.of_fin 364000 200 complete_chunk1820

lemma complete_chunk1821 : ∀ i : Fin 200, Compatible (364200 + i.val) →
    (table.lookup (364200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1821 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 364200 364400 :=
  FiniteIntervals.of_fin 364200 200 complete_chunk1821

lemma complete_chunk1822 : ∀ i : Fin 200, Compatible (364400 + i.val) →
    (table.lookup (364400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1822 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 364400 364600 :=
  FiniteIntervals.of_fin 364400 200 complete_chunk1822

lemma complete_chunk1823 : ∀ i : Fin 200, Compatible (364600 + i.val) →
    (table.lookup (364600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1823 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 364600 364800 :=
  FiniteIntervals.of_fin 364600 200 complete_chunk1823

lemma complete_chunk1824 : ∀ i : Fin 200, Compatible (364800 + i.val) →
    (table.lookup (364800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1824 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 364800 365000 :=
  FiniteIntervals.of_fin 364800 200 complete_chunk1824

lemma complete_chunk1825 : ∀ i : Fin 200, Compatible (365000 + i.val) →
    (table.lookup (365000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1825 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 365000 365200 :=
  FiniteIntervals.of_fin 365000 200 complete_chunk1825

lemma complete_chunk1826 : ∀ i : Fin 200, Compatible (365200 + i.val) →
    (table.lookup (365200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1826 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 365200 365400 :=
  FiniteIntervals.of_fin 365200 200 complete_chunk1826

lemma complete_chunk1827 : ∀ i : Fin 200, Compatible (365400 + i.val) →
    (table.lookup (365400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1827 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 365400 365600 :=
  FiniteIntervals.of_fin 365400 200 complete_chunk1827

lemma complete_chunk1828 : ∀ i : Fin 200, Compatible (365600 + i.val) →
    (table.lookup (365600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1828 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 365600 365800 :=
  FiniteIntervals.of_fin 365600 200 complete_chunk1828

lemma complete_chunk1829 : ∀ i : Fin 200, Compatible (365800 + i.val) →
    (table.lookup (365800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1829 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 365800 366000 :=
  FiniteIntervals.of_fin 365800 200 complete_chunk1829

#print axioms interval_chunk1820
end Erdos184Work.PureFiveFilter4
