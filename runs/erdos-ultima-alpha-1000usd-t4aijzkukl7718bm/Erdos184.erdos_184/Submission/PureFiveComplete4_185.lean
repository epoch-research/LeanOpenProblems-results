import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1850 : ∀ i : Fin 200, Compatible (370000 + i.val) →
    (table.lookup (370000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1850 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 370000 370200 :=
  FiniteIntervals.of_fin 370000 200 complete_chunk1850

lemma complete_chunk1851 : ∀ i : Fin 200, Compatible (370200 + i.val) →
    (table.lookup (370200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1851 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 370200 370400 :=
  FiniteIntervals.of_fin 370200 200 complete_chunk1851

lemma complete_chunk1852 : ∀ i : Fin 200, Compatible (370400 + i.val) →
    (table.lookup (370400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1852 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 370400 370600 :=
  FiniteIntervals.of_fin 370400 200 complete_chunk1852

lemma complete_chunk1853 : ∀ i : Fin 200, Compatible (370600 + i.val) →
    (table.lookup (370600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1853 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 370600 370800 :=
  FiniteIntervals.of_fin 370600 200 complete_chunk1853

lemma complete_chunk1854 : ∀ i : Fin 200, Compatible (370800 + i.val) →
    (table.lookup (370800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1854 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 370800 371000 :=
  FiniteIntervals.of_fin 370800 200 complete_chunk1854

lemma complete_chunk1855 : ∀ i : Fin 200, Compatible (371000 + i.val) →
    (table.lookup (371000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1855 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 371000 371200 :=
  FiniteIntervals.of_fin 371000 200 complete_chunk1855

lemma complete_chunk1856 : ∀ i : Fin 200, Compatible (371200 + i.val) →
    (table.lookup (371200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1856 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 371200 371400 :=
  FiniteIntervals.of_fin 371200 200 complete_chunk1856

lemma complete_chunk1857 : ∀ i : Fin 200, Compatible (371400 + i.val) →
    (table.lookup (371400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1857 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 371400 371600 :=
  FiniteIntervals.of_fin 371400 200 complete_chunk1857

lemma complete_chunk1858 : ∀ i : Fin 200, Compatible (371600 + i.val) →
    (table.lookup (371600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1858 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 371600 371800 :=
  FiniteIntervals.of_fin 371600 200 complete_chunk1858

lemma complete_chunk1859 : ∀ i : Fin 200, Compatible (371800 + i.val) →
    (table.lookup (371800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1859 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 371800 372000 :=
  FiniteIntervals.of_fin 371800 200 complete_chunk1859

#print axioms interval_chunk1850
end Erdos184Work.PureFiveFilter4
