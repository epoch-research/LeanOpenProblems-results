import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk630 : ∀ i : Fin 200, Compatible (126000 + i.val) →
    (table.lookup (126000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk630 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 126000 126200 :=
  FiniteIntervals.of_fin 126000 200 complete_chunk630

lemma complete_chunk631 : ∀ i : Fin 200, Compatible (126200 + i.val) →
    (table.lookup (126200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk631 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 126200 126400 :=
  FiniteIntervals.of_fin 126200 200 complete_chunk631

lemma complete_chunk632 : ∀ i : Fin 200, Compatible (126400 + i.val) →
    (table.lookup (126400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk632 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 126400 126600 :=
  FiniteIntervals.of_fin 126400 200 complete_chunk632

lemma complete_chunk633 : ∀ i : Fin 200, Compatible (126600 + i.val) →
    (table.lookup (126600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk633 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 126600 126800 :=
  FiniteIntervals.of_fin 126600 200 complete_chunk633

lemma complete_chunk634 : ∀ i : Fin 200, Compatible (126800 + i.val) →
    (table.lookup (126800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk634 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 126800 127000 :=
  FiniteIntervals.of_fin 126800 200 complete_chunk634

lemma complete_chunk635 : ∀ i : Fin 200, Compatible (127000 + i.val) →
    (table.lookup (127000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk635 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 127000 127200 :=
  FiniteIntervals.of_fin 127000 200 complete_chunk635

lemma complete_chunk636 : ∀ i : Fin 200, Compatible (127200 + i.val) →
    (table.lookup (127200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk636 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 127200 127400 :=
  FiniteIntervals.of_fin 127200 200 complete_chunk636

lemma complete_chunk637 : ∀ i : Fin 200, Compatible (127400 + i.val) →
    (table.lookup (127400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk637 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 127400 127600 :=
  FiniteIntervals.of_fin 127400 200 complete_chunk637

lemma complete_chunk638 : ∀ i : Fin 200, Compatible (127600 + i.val) →
    (table.lookup (127600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk638 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 127600 127800 :=
  FiniteIntervals.of_fin 127600 200 complete_chunk638

lemma complete_chunk639 : ∀ i : Fin 200, Compatible (127800 + i.val) →
    (table.lookup (127800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk639 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 127800 128000 :=
  FiniteIntervals.of_fin 127800 200 complete_chunk639

#print axioms interval_chunk630
end Erdos184Work.PureFiveFilter4
