import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk800 : ∀ i : Fin 200, Compatible (160000 + i.val) →
    (table.lookup (160000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk800 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 160000 160200 :=
  FiniteIntervals.of_fin 160000 200 complete_chunk800

lemma complete_chunk801 : ∀ i : Fin 200, Compatible (160200 + i.val) →
    (table.lookup (160200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk801 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 160200 160400 :=
  FiniteIntervals.of_fin 160200 200 complete_chunk801

lemma complete_chunk802 : ∀ i : Fin 200, Compatible (160400 + i.val) →
    (table.lookup (160400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk802 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 160400 160600 :=
  FiniteIntervals.of_fin 160400 200 complete_chunk802

lemma complete_chunk803 : ∀ i : Fin 200, Compatible (160600 + i.val) →
    (table.lookup (160600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk803 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 160600 160800 :=
  FiniteIntervals.of_fin 160600 200 complete_chunk803

lemma complete_chunk804 : ∀ i : Fin 200, Compatible (160800 + i.val) →
    (table.lookup (160800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk804 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 160800 161000 :=
  FiniteIntervals.of_fin 160800 200 complete_chunk804

lemma complete_chunk805 : ∀ i : Fin 200, Compatible (161000 + i.val) →
    (table.lookup (161000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk805 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 161000 161200 :=
  FiniteIntervals.of_fin 161000 200 complete_chunk805

lemma complete_chunk806 : ∀ i : Fin 200, Compatible (161200 + i.val) →
    (table.lookup (161200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk806 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 161200 161400 :=
  FiniteIntervals.of_fin 161200 200 complete_chunk806

lemma complete_chunk807 : ∀ i : Fin 200, Compatible (161400 + i.val) →
    (table.lookup (161400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk807 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 161400 161600 :=
  FiniteIntervals.of_fin 161400 200 complete_chunk807

lemma complete_chunk808 : ∀ i : Fin 200, Compatible (161600 + i.val) →
    (table.lookup (161600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk808 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 161600 161800 :=
  FiniteIntervals.of_fin 161600 200 complete_chunk808

lemma complete_chunk809 : ∀ i : Fin 200, Compatible (161800 + i.val) →
    (table.lookup (161800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk809 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 161800 162000 :=
  FiniteIntervals.of_fin 161800 200 complete_chunk809

#print axioms interval_chunk800
end Erdos184Work.PureFiveFilter4
