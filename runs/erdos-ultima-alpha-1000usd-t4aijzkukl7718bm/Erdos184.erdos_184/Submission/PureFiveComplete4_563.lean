import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5630 : ∀ i : Fin 200, Compatible (1126000 + i.val) →
    (table.lookup (1126000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5630 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1126000 1126200 :=
  FiniteIntervals.of_fin 1126000 200 complete_chunk5630

lemma complete_chunk5631 : ∀ i : Fin 200, Compatible (1126200 + i.val) →
    (table.lookup (1126200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5631 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1126200 1126400 :=
  FiniteIntervals.of_fin 1126200 200 complete_chunk5631

lemma complete_chunk5632 : ∀ i : Fin 200, Compatible (1126400 + i.val) →
    (table.lookup (1126400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5632 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1126400 1126600 :=
  FiniteIntervals.of_fin 1126400 200 complete_chunk5632

lemma complete_chunk5633 : ∀ i : Fin 200, Compatible (1126600 + i.val) →
    (table.lookup (1126600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5633 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1126600 1126800 :=
  FiniteIntervals.of_fin 1126600 200 complete_chunk5633

lemma complete_chunk5634 : ∀ i : Fin 200, Compatible (1126800 + i.val) →
    (table.lookup (1126800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5634 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1126800 1127000 :=
  FiniteIntervals.of_fin 1126800 200 complete_chunk5634

lemma complete_chunk5635 : ∀ i : Fin 200, Compatible (1127000 + i.val) →
    (table.lookup (1127000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5635 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1127000 1127200 :=
  FiniteIntervals.of_fin 1127000 200 complete_chunk5635

lemma complete_chunk5636 : ∀ i : Fin 200, Compatible (1127200 + i.val) →
    (table.lookup (1127200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5636 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1127200 1127400 :=
  FiniteIntervals.of_fin 1127200 200 complete_chunk5636

lemma complete_chunk5637 : ∀ i : Fin 200, Compatible (1127400 + i.val) →
    (table.lookup (1127400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5637 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1127400 1127600 :=
  FiniteIntervals.of_fin 1127400 200 complete_chunk5637

lemma complete_chunk5638 : ∀ i : Fin 200, Compatible (1127600 + i.val) →
    (table.lookup (1127600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5638 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1127600 1127800 :=
  FiniteIntervals.of_fin 1127600 200 complete_chunk5638

lemma complete_chunk5639 : ∀ i : Fin 200, Compatible (1127800 + i.val) →
    (table.lookup (1127800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5639 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1127800 1128000 :=
  FiniteIntervals.of_fin 1127800 200 complete_chunk5639

#print axioms interval_chunk5630
end Erdos184Work.PureFiveFilter4
