import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3740 : ∀ i : Fin 200, Compatible (748000 + i.val) →
    (table.lookup (748000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3740 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 748000 748200 :=
  FiniteIntervals.of_fin 748000 200 complete_chunk3740

lemma complete_chunk3741 : ∀ i : Fin 200, Compatible (748200 + i.val) →
    (table.lookup (748200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3741 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 748200 748400 :=
  FiniteIntervals.of_fin 748200 200 complete_chunk3741

lemma complete_chunk3742 : ∀ i : Fin 200, Compatible (748400 + i.val) →
    (table.lookup (748400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3742 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 748400 748600 :=
  FiniteIntervals.of_fin 748400 200 complete_chunk3742

lemma complete_chunk3743 : ∀ i : Fin 200, Compatible (748600 + i.val) →
    (table.lookup (748600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3743 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 748600 748800 :=
  FiniteIntervals.of_fin 748600 200 complete_chunk3743

lemma complete_chunk3744 : ∀ i : Fin 200, Compatible (748800 + i.val) →
    (table.lookup (748800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3744 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 748800 749000 :=
  FiniteIntervals.of_fin 748800 200 complete_chunk3744

lemma complete_chunk3745 : ∀ i : Fin 200, Compatible (749000 + i.val) →
    (table.lookup (749000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3745 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 749000 749200 :=
  FiniteIntervals.of_fin 749000 200 complete_chunk3745

lemma complete_chunk3746 : ∀ i : Fin 200, Compatible (749200 + i.val) →
    (table.lookup (749200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3746 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 749200 749400 :=
  FiniteIntervals.of_fin 749200 200 complete_chunk3746

lemma complete_chunk3747 : ∀ i : Fin 200, Compatible (749400 + i.val) →
    (table.lookup (749400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3747 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 749400 749600 :=
  FiniteIntervals.of_fin 749400 200 complete_chunk3747

lemma complete_chunk3748 : ∀ i : Fin 200, Compatible (749600 + i.val) →
    (table.lookup (749600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3748 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 749600 749800 :=
  FiniteIntervals.of_fin 749600 200 complete_chunk3748

lemma complete_chunk3749 : ∀ i : Fin 200, Compatible (749800 + i.val) →
    (table.lookup (749800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3749 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 749800 750000 :=
  FiniteIntervals.of_fin 749800 200 complete_chunk3749

#print axioms interval_chunk3740
end Erdos184Work.PureFiveFilter4
