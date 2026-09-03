import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5760 : ∀ i : Fin 200, Compatible (1152000 + i.val) →
    (table.lookup (1152000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5760 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1152000 1152200 :=
  FiniteIntervals.of_fin 1152000 200 complete_chunk5760

lemma complete_chunk5761 : ∀ i : Fin 200, Compatible (1152200 + i.val) →
    (table.lookup (1152200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5761 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1152200 1152400 :=
  FiniteIntervals.of_fin 1152200 200 complete_chunk5761

lemma complete_chunk5762 : ∀ i : Fin 200, Compatible (1152400 + i.val) →
    (table.lookup (1152400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5762 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1152400 1152600 :=
  FiniteIntervals.of_fin 1152400 200 complete_chunk5762

lemma complete_chunk5763 : ∀ i : Fin 200, Compatible (1152600 + i.val) →
    (table.lookup (1152600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5763 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1152600 1152800 :=
  FiniteIntervals.of_fin 1152600 200 complete_chunk5763

lemma complete_chunk5764 : ∀ i : Fin 200, Compatible (1152800 + i.val) →
    (table.lookup (1152800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5764 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1152800 1153000 :=
  FiniteIntervals.of_fin 1152800 200 complete_chunk5764

lemma complete_chunk5765 : ∀ i : Fin 200, Compatible (1153000 + i.val) →
    (table.lookup (1153000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5765 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1153000 1153200 :=
  FiniteIntervals.of_fin 1153000 200 complete_chunk5765

lemma complete_chunk5766 : ∀ i : Fin 200, Compatible (1153200 + i.val) →
    (table.lookup (1153200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5766 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1153200 1153400 :=
  FiniteIntervals.of_fin 1153200 200 complete_chunk5766

lemma complete_chunk5767 : ∀ i : Fin 200, Compatible (1153400 + i.val) →
    (table.lookup (1153400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5767 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1153400 1153600 :=
  FiniteIntervals.of_fin 1153400 200 complete_chunk5767

lemma complete_chunk5768 : ∀ i : Fin 200, Compatible (1153600 + i.val) →
    (table.lookup (1153600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5768 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1153600 1153800 :=
  FiniteIntervals.of_fin 1153600 200 complete_chunk5768

lemma complete_chunk5769 : ∀ i : Fin 200, Compatible (1153800 + i.val) →
    (table.lookup (1153800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5769 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1153800 1154000 :=
  FiniteIntervals.of_fin 1153800 200 complete_chunk5769

#print axioms interval_chunk5760
end Erdos184Work.PureFiveFilter4
