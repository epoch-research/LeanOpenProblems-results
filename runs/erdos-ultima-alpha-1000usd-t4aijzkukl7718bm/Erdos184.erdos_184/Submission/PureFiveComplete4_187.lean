import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1870 : ∀ i : Fin 200, Compatible (374000 + i.val) →
    (table.lookup (374000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1870 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 374000 374200 :=
  FiniteIntervals.of_fin 374000 200 complete_chunk1870

lemma complete_chunk1871 : ∀ i : Fin 200, Compatible (374200 + i.val) →
    (table.lookup (374200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1871 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 374200 374400 :=
  FiniteIntervals.of_fin 374200 200 complete_chunk1871

lemma complete_chunk1872 : ∀ i : Fin 200, Compatible (374400 + i.val) →
    (table.lookup (374400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1872 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 374400 374600 :=
  FiniteIntervals.of_fin 374400 200 complete_chunk1872

lemma complete_chunk1873 : ∀ i : Fin 200, Compatible (374600 + i.val) →
    (table.lookup (374600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1873 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 374600 374800 :=
  FiniteIntervals.of_fin 374600 200 complete_chunk1873

lemma complete_chunk1874 : ∀ i : Fin 200, Compatible (374800 + i.val) →
    (table.lookup (374800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1874 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 374800 375000 :=
  FiniteIntervals.of_fin 374800 200 complete_chunk1874

lemma complete_chunk1875 : ∀ i : Fin 200, Compatible (375000 + i.val) →
    (table.lookup (375000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1875 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 375000 375200 :=
  FiniteIntervals.of_fin 375000 200 complete_chunk1875

lemma complete_chunk1876 : ∀ i : Fin 200, Compatible (375200 + i.val) →
    (table.lookup (375200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1876 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 375200 375400 :=
  FiniteIntervals.of_fin 375200 200 complete_chunk1876

lemma complete_chunk1877 : ∀ i : Fin 200, Compatible (375400 + i.val) →
    (table.lookup (375400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1877 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 375400 375600 :=
  FiniteIntervals.of_fin 375400 200 complete_chunk1877

lemma complete_chunk1878 : ∀ i : Fin 200, Compatible (375600 + i.val) →
    (table.lookup (375600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1878 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 375600 375800 :=
  FiniteIntervals.of_fin 375600 200 complete_chunk1878

lemma complete_chunk1879 : ∀ i : Fin 200, Compatible (375800 + i.val) →
    (table.lookup (375800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1879 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 375800 376000 :=
  FiniteIntervals.of_fin 375800 200 complete_chunk1879

#print axioms interval_chunk1870
end Erdos184Work.PureFiveFilter4
