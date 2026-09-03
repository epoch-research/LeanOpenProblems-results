import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5730 : ∀ i : Fin 200, Compatible (1146000 + i.val) →
    (table.lookup (1146000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5730 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1146000 1146200 :=
  FiniteIntervals.of_fin 1146000 200 complete_chunk5730

lemma complete_chunk5731 : ∀ i : Fin 200, Compatible (1146200 + i.val) →
    (table.lookup (1146200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5731 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1146200 1146400 :=
  FiniteIntervals.of_fin 1146200 200 complete_chunk5731

lemma complete_chunk5732 : ∀ i : Fin 200, Compatible (1146400 + i.val) →
    (table.lookup (1146400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5732 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1146400 1146600 :=
  FiniteIntervals.of_fin 1146400 200 complete_chunk5732

lemma complete_chunk5733 : ∀ i : Fin 200, Compatible (1146600 + i.val) →
    (table.lookup (1146600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5733 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1146600 1146800 :=
  FiniteIntervals.of_fin 1146600 200 complete_chunk5733

lemma complete_chunk5734 : ∀ i : Fin 200, Compatible (1146800 + i.val) →
    (table.lookup (1146800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5734 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1146800 1147000 :=
  FiniteIntervals.of_fin 1146800 200 complete_chunk5734

lemma complete_chunk5735 : ∀ i : Fin 200, Compatible (1147000 + i.val) →
    (table.lookup (1147000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5735 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1147000 1147200 :=
  FiniteIntervals.of_fin 1147000 200 complete_chunk5735

lemma complete_chunk5736 : ∀ i : Fin 200, Compatible (1147200 + i.val) →
    (table.lookup (1147200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5736 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1147200 1147400 :=
  FiniteIntervals.of_fin 1147200 200 complete_chunk5736

lemma complete_chunk5737 : ∀ i : Fin 200, Compatible (1147400 + i.val) →
    (table.lookup (1147400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5737 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1147400 1147600 :=
  FiniteIntervals.of_fin 1147400 200 complete_chunk5737

lemma complete_chunk5738 : ∀ i : Fin 200, Compatible (1147600 + i.val) →
    (table.lookup (1147600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5738 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1147600 1147800 :=
  FiniteIntervals.of_fin 1147600 200 complete_chunk5738

lemma complete_chunk5739 : ∀ i : Fin 200, Compatible (1147800 + i.val) →
    (table.lookup (1147800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5739 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1147800 1148000 :=
  FiniteIntervals.of_fin 1147800 200 complete_chunk5739

#print axioms interval_chunk5730
end Erdos184Work.PureFiveFilter4
