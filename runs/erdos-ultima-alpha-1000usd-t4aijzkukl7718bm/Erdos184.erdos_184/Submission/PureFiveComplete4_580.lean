import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5800 : ∀ i : Fin 200, Compatible (1160000 + i.val) →
    (table.lookup (1160000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5800 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1160000 1160200 :=
  FiniteIntervals.of_fin 1160000 200 complete_chunk5800

lemma complete_chunk5801 : ∀ i : Fin 200, Compatible (1160200 + i.val) →
    (table.lookup (1160200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5801 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1160200 1160400 :=
  FiniteIntervals.of_fin 1160200 200 complete_chunk5801

lemma complete_chunk5802 : ∀ i : Fin 200, Compatible (1160400 + i.val) →
    (table.lookup (1160400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5802 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1160400 1160600 :=
  FiniteIntervals.of_fin 1160400 200 complete_chunk5802

lemma complete_chunk5803 : ∀ i : Fin 200, Compatible (1160600 + i.val) →
    (table.lookup (1160600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5803 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1160600 1160800 :=
  FiniteIntervals.of_fin 1160600 200 complete_chunk5803

lemma complete_chunk5804 : ∀ i : Fin 200, Compatible (1160800 + i.val) →
    (table.lookup (1160800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5804 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1160800 1161000 :=
  FiniteIntervals.of_fin 1160800 200 complete_chunk5804

lemma complete_chunk5805 : ∀ i : Fin 200, Compatible (1161000 + i.val) →
    (table.lookup (1161000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5805 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1161000 1161200 :=
  FiniteIntervals.of_fin 1161000 200 complete_chunk5805

lemma complete_chunk5806 : ∀ i : Fin 200, Compatible (1161200 + i.val) →
    (table.lookup (1161200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5806 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1161200 1161400 :=
  FiniteIntervals.of_fin 1161200 200 complete_chunk5806

lemma complete_chunk5807 : ∀ i : Fin 200, Compatible (1161400 + i.val) →
    (table.lookup (1161400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5807 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1161400 1161600 :=
  FiniteIntervals.of_fin 1161400 200 complete_chunk5807

lemma complete_chunk5808 : ∀ i : Fin 200, Compatible (1161600 + i.val) →
    (table.lookup (1161600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5808 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1161600 1161800 :=
  FiniteIntervals.of_fin 1161600 200 complete_chunk5808

lemma complete_chunk5809 : ∀ i : Fin 200, Compatible (1161800 + i.val) →
    (table.lookup (1161800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5809 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1161800 1162000 :=
  FiniteIntervals.of_fin 1161800 200 complete_chunk5809

#print axioms interval_chunk5800
end Erdos184Work.PureFiveFilter4
