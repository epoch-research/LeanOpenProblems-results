import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1830 : ∀ i : Fin 200, Compatible (366000 + i.val) →
    (table.lookup (366000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1830 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 366000 366200 :=
  FiniteIntervals.of_fin 366000 200 complete_chunk1830

lemma complete_chunk1831 : ∀ i : Fin 200, Compatible (366200 + i.val) →
    (table.lookup (366200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1831 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 366200 366400 :=
  FiniteIntervals.of_fin 366200 200 complete_chunk1831

lemma complete_chunk1832 : ∀ i : Fin 200, Compatible (366400 + i.val) →
    (table.lookup (366400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1832 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 366400 366600 :=
  FiniteIntervals.of_fin 366400 200 complete_chunk1832

lemma complete_chunk1833 : ∀ i : Fin 200, Compatible (366600 + i.val) →
    (table.lookup (366600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1833 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 366600 366800 :=
  FiniteIntervals.of_fin 366600 200 complete_chunk1833

lemma complete_chunk1834 : ∀ i : Fin 200, Compatible (366800 + i.val) →
    (table.lookup (366800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1834 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 366800 367000 :=
  FiniteIntervals.of_fin 366800 200 complete_chunk1834

lemma complete_chunk1835 : ∀ i : Fin 200, Compatible (367000 + i.val) →
    (table.lookup (367000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1835 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 367000 367200 :=
  FiniteIntervals.of_fin 367000 200 complete_chunk1835

lemma complete_chunk1836 : ∀ i : Fin 200, Compatible (367200 + i.val) →
    (table.lookup (367200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1836 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 367200 367400 :=
  FiniteIntervals.of_fin 367200 200 complete_chunk1836

lemma complete_chunk1837 : ∀ i : Fin 200, Compatible (367400 + i.val) →
    (table.lookup (367400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1837 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 367400 367600 :=
  FiniteIntervals.of_fin 367400 200 complete_chunk1837

lemma complete_chunk1838 : ∀ i : Fin 200, Compatible (367600 + i.val) →
    (table.lookup (367600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1838 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 367600 367800 :=
  FiniteIntervals.of_fin 367600 200 complete_chunk1838

lemma complete_chunk1839 : ∀ i : Fin 200, Compatible (367800 + i.val) →
    (table.lookup (367800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1839 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 367800 368000 :=
  FiniteIntervals.of_fin 367800 200 complete_chunk1839

#print axioms interval_chunk1830
end Erdos184Work.PureFiveFilter4
