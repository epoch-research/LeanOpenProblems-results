import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk730 : ∀ i : Fin 200, Compatible (146000 + i.val) →
    (table.lookup (146000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk730 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 146000 146200 :=
  FiniteIntervals.of_fin 146000 200 complete_chunk730

lemma complete_chunk731 : ∀ i : Fin 200, Compatible (146200 + i.val) →
    (table.lookup (146200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk731 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 146200 146400 :=
  FiniteIntervals.of_fin 146200 200 complete_chunk731

lemma complete_chunk732 : ∀ i : Fin 200, Compatible (146400 + i.val) →
    (table.lookup (146400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk732 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 146400 146600 :=
  FiniteIntervals.of_fin 146400 200 complete_chunk732

lemma complete_chunk733 : ∀ i : Fin 200, Compatible (146600 + i.val) →
    (table.lookup (146600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk733 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 146600 146800 :=
  FiniteIntervals.of_fin 146600 200 complete_chunk733

lemma complete_chunk734 : ∀ i : Fin 200, Compatible (146800 + i.val) →
    (table.lookup (146800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk734 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 146800 147000 :=
  FiniteIntervals.of_fin 146800 200 complete_chunk734

lemma complete_chunk735 : ∀ i : Fin 200, Compatible (147000 + i.val) →
    (table.lookup (147000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk735 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 147000 147200 :=
  FiniteIntervals.of_fin 147000 200 complete_chunk735

lemma complete_chunk736 : ∀ i : Fin 200, Compatible (147200 + i.val) →
    (table.lookup (147200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk736 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 147200 147400 :=
  FiniteIntervals.of_fin 147200 200 complete_chunk736

lemma complete_chunk737 : ∀ i : Fin 200, Compatible (147400 + i.val) →
    (table.lookup (147400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk737 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 147400 147600 :=
  FiniteIntervals.of_fin 147400 200 complete_chunk737

lemma complete_chunk738 : ∀ i : Fin 200, Compatible (147600 + i.val) →
    (table.lookup (147600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk738 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 147600 147800 :=
  FiniteIntervals.of_fin 147600 200 complete_chunk738

lemma complete_chunk739 : ∀ i : Fin 200, Compatible (147800 + i.val) →
    (table.lookup (147800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk739 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 147800 148000 :=
  FiniteIntervals.of_fin 147800 200 complete_chunk739

#print axioms interval_chunk730
end Erdos184Work.PureFiveFilter4
