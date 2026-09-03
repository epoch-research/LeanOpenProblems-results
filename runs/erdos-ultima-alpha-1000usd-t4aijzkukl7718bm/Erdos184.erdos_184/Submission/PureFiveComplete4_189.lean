import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1890 : ∀ i : Fin 200, Compatible (378000 + i.val) →
    (table.lookup (378000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1890 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 378000 378200 :=
  FiniteIntervals.of_fin 378000 200 complete_chunk1890

lemma complete_chunk1891 : ∀ i : Fin 200, Compatible (378200 + i.val) →
    (table.lookup (378200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1891 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 378200 378400 :=
  FiniteIntervals.of_fin 378200 200 complete_chunk1891

lemma complete_chunk1892 : ∀ i : Fin 200, Compatible (378400 + i.val) →
    (table.lookup (378400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1892 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 378400 378600 :=
  FiniteIntervals.of_fin 378400 200 complete_chunk1892

lemma complete_chunk1893 : ∀ i : Fin 200, Compatible (378600 + i.val) →
    (table.lookup (378600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1893 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 378600 378800 :=
  FiniteIntervals.of_fin 378600 200 complete_chunk1893

lemma complete_chunk1894 : ∀ i : Fin 200, Compatible (378800 + i.val) →
    (table.lookup (378800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1894 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 378800 379000 :=
  FiniteIntervals.of_fin 378800 200 complete_chunk1894

lemma complete_chunk1895 : ∀ i : Fin 200, Compatible (379000 + i.val) →
    (table.lookup (379000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1895 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 379000 379200 :=
  FiniteIntervals.of_fin 379000 200 complete_chunk1895

lemma complete_chunk1896 : ∀ i : Fin 200, Compatible (379200 + i.val) →
    (table.lookup (379200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1896 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 379200 379400 :=
  FiniteIntervals.of_fin 379200 200 complete_chunk1896

lemma complete_chunk1897 : ∀ i : Fin 200, Compatible (379400 + i.val) →
    (table.lookup (379400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1897 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 379400 379600 :=
  FiniteIntervals.of_fin 379400 200 complete_chunk1897

lemma complete_chunk1898 : ∀ i : Fin 200, Compatible (379600 + i.val) →
    (table.lookup (379600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1898 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 379600 379800 :=
  FiniteIntervals.of_fin 379600 200 complete_chunk1898

lemma complete_chunk1899 : ∀ i : Fin 200, Compatible (379800 + i.val) →
    (table.lookup (379800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1899 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 379800 380000 :=
  FiniteIntervals.of_fin 379800 200 complete_chunk1899

#print axioms interval_chunk1890
end Erdos184Work.PureFiveFilter4
