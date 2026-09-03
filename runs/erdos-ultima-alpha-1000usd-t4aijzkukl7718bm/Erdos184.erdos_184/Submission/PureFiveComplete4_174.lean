import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1740 : ∀ i : Fin 200, Compatible (348000 + i.val) →
    (table.lookup (348000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1740 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 348000 348200 :=
  FiniteIntervals.of_fin 348000 200 complete_chunk1740

lemma complete_chunk1741 : ∀ i : Fin 200, Compatible (348200 + i.val) →
    (table.lookup (348200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1741 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 348200 348400 :=
  FiniteIntervals.of_fin 348200 200 complete_chunk1741

lemma complete_chunk1742 : ∀ i : Fin 200, Compatible (348400 + i.val) →
    (table.lookup (348400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1742 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 348400 348600 :=
  FiniteIntervals.of_fin 348400 200 complete_chunk1742

lemma complete_chunk1743 : ∀ i : Fin 200, Compatible (348600 + i.val) →
    (table.lookup (348600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1743 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 348600 348800 :=
  FiniteIntervals.of_fin 348600 200 complete_chunk1743

lemma complete_chunk1744 : ∀ i : Fin 200, Compatible (348800 + i.val) →
    (table.lookup (348800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1744 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 348800 349000 :=
  FiniteIntervals.of_fin 348800 200 complete_chunk1744

lemma complete_chunk1745 : ∀ i : Fin 200, Compatible (349000 + i.val) →
    (table.lookup (349000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1745 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 349000 349200 :=
  FiniteIntervals.of_fin 349000 200 complete_chunk1745

lemma complete_chunk1746 : ∀ i : Fin 200, Compatible (349200 + i.val) →
    (table.lookup (349200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1746 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 349200 349400 :=
  FiniteIntervals.of_fin 349200 200 complete_chunk1746

lemma complete_chunk1747 : ∀ i : Fin 200, Compatible (349400 + i.val) →
    (table.lookup (349400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1747 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 349400 349600 :=
  FiniteIntervals.of_fin 349400 200 complete_chunk1747

lemma complete_chunk1748 : ∀ i : Fin 200, Compatible (349600 + i.val) →
    (table.lookup (349600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1748 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 349600 349800 :=
  FiniteIntervals.of_fin 349600 200 complete_chunk1748

lemma complete_chunk1749 : ∀ i : Fin 200, Compatible (349800 + i.val) →
    (table.lookup (349800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1749 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 349800 350000 :=
  FiniteIntervals.of_fin 349800 200 complete_chunk1749

#print axioms interval_chunk1740
end Erdos184Work.PureFiveFilter4
