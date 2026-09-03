import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1880 : ∀ i : Fin 200, Compatible (376000 + i.val) →
    (table.lookup (376000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1880 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 376000 376200 :=
  FiniteIntervals.of_fin 376000 200 complete_chunk1880

lemma complete_chunk1881 : ∀ i : Fin 200, Compatible (376200 + i.val) →
    (table.lookup (376200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1881 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 376200 376400 :=
  FiniteIntervals.of_fin 376200 200 complete_chunk1881

lemma complete_chunk1882 : ∀ i : Fin 200, Compatible (376400 + i.val) →
    (table.lookup (376400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1882 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 376400 376600 :=
  FiniteIntervals.of_fin 376400 200 complete_chunk1882

lemma complete_chunk1883 : ∀ i : Fin 200, Compatible (376600 + i.val) →
    (table.lookup (376600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1883 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 376600 376800 :=
  FiniteIntervals.of_fin 376600 200 complete_chunk1883

lemma complete_chunk1884 : ∀ i : Fin 200, Compatible (376800 + i.val) →
    (table.lookup (376800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1884 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 376800 377000 :=
  FiniteIntervals.of_fin 376800 200 complete_chunk1884

lemma complete_chunk1885 : ∀ i : Fin 200, Compatible (377000 + i.val) →
    (table.lookup (377000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1885 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 377000 377200 :=
  FiniteIntervals.of_fin 377000 200 complete_chunk1885

lemma complete_chunk1886 : ∀ i : Fin 200, Compatible (377200 + i.val) →
    (table.lookup (377200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1886 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 377200 377400 :=
  FiniteIntervals.of_fin 377200 200 complete_chunk1886

lemma complete_chunk1887 : ∀ i : Fin 200, Compatible (377400 + i.val) →
    (table.lookup (377400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1887 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 377400 377600 :=
  FiniteIntervals.of_fin 377400 200 complete_chunk1887

lemma complete_chunk1888 : ∀ i : Fin 200, Compatible (377600 + i.val) →
    (table.lookup (377600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1888 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 377600 377800 :=
  FiniteIntervals.of_fin 377600 200 complete_chunk1888

lemma complete_chunk1889 : ∀ i : Fin 200, Compatible (377800 + i.val) →
    (table.lookup (377800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1889 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 377800 378000 :=
  FiniteIntervals.of_fin 377800 200 complete_chunk1889

#print axioms interval_chunk1880
end Erdos184Work.PureFiveFilter4
