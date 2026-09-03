import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk760 : ∀ i : Fin 200, Compatible (152000 + i.val) →
    (table.lookup (152000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk760 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 152000 152200 :=
  FiniteIntervals.of_fin 152000 200 complete_chunk760

lemma complete_chunk761 : ∀ i : Fin 200, Compatible (152200 + i.val) →
    (table.lookup (152200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk761 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 152200 152400 :=
  FiniteIntervals.of_fin 152200 200 complete_chunk761

lemma complete_chunk762 : ∀ i : Fin 200, Compatible (152400 + i.val) →
    (table.lookup (152400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk762 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 152400 152600 :=
  FiniteIntervals.of_fin 152400 200 complete_chunk762

lemma complete_chunk763 : ∀ i : Fin 200, Compatible (152600 + i.val) →
    (table.lookup (152600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk763 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 152600 152800 :=
  FiniteIntervals.of_fin 152600 200 complete_chunk763

lemma complete_chunk764 : ∀ i : Fin 200, Compatible (152800 + i.val) →
    (table.lookup (152800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk764 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 152800 153000 :=
  FiniteIntervals.of_fin 152800 200 complete_chunk764

lemma complete_chunk765 : ∀ i : Fin 200, Compatible (153000 + i.val) →
    (table.lookup (153000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk765 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 153000 153200 :=
  FiniteIntervals.of_fin 153000 200 complete_chunk765

lemma complete_chunk766 : ∀ i : Fin 200, Compatible (153200 + i.val) →
    (table.lookup (153200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk766 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 153200 153400 :=
  FiniteIntervals.of_fin 153200 200 complete_chunk766

lemma complete_chunk767 : ∀ i : Fin 200, Compatible (153400 + i.val) →
    (table.lookup (153400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk767 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 153400 153600 :=
  FiniteIntervals.of_fin 153400 200 complete_chunk767

lemma complete_chunk768 : ∀ i : Fin 200, Compatible (153600 + i.val) →
    (table.lookup (153600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk768 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 153600 153800 :=
  FiniteIntervals.of_fin 153600 200 complete_chunk768

lemma complete_chunk769 : ∀ i : Fin 200, Compatible (153800 + i.val) →
    (table.lookup (153800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk769 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 153800 154000 :=
  FiniteIntervals.of_fin 153800 200 complete_chunk769

#print axioms interval_chunk760
end Erdos184Work.PureFiveFilter4
