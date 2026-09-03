import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3730 : ∀ i : Fin 200, Compatible (746000 + i.val) →
    (table.lookup (746000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3730 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 746000 746200 :=
  FiniteIntervals.of_fin 746000 200 complete_chunk3730

lemma complete_chunk3731 : ∀ i : Fin 200, Compatible (746200 + i.val) →
    (table.lookup (746200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3731 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 746200 746400 :=
  FiniteIntervals.of_fin 746200 200 complete_chunk3731

lemma complete_chunk3732 : ∀ i : Fin 200, Compatible (746400 + i.val) →
    (table.lookup (746400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3732 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 746400 746600 :=
  FiniteIntervals.of_fin 746400 200 complete_chunk3732

lemma complete_chunk3733 : ∀ i : Fin 200, Compatible (746600 + i.val) →
    (table.lookup (746600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3733 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 746600 746800 :=
  FiniteIntervals.of_fin 746600 200 complete_chunk3733

lemma complete_chunk3734 : ∀ i : Fin 200, Compatible (746800 + i.val) →
    (table.lookup (746800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3734 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 746800 747000 :=
  FiniteIntervals.of_fin 746800 200 complete_chunk3734

lemma complete_chunk3735 : ∀ i : Fin 200, Compatible (747000 + i.val) →
    (table.lookup (747000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3735 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 747000 747200 :=
  FiniteIntervals.of_fin 747000 200 complete_chunk3735

lemma complete_chunk3736 : ∀ i : Fin 200, Compatible (747200 + i.val) →
    (table.lookup (747200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3736 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 747200 747400 :=
  FiniteIntervals.of_fin 747200 200 complete_chunk3736

lemma complete_chunk3737 : ∀ i : Fin 200, Compatible (747400 + i.val) →
    (table.lookup (747400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3737 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 747400 747600 :=
  FiniteIntervals.of_fin 747400 200 complete_chunk3737

lemma complete_chunk3738 : ∀ i : Fin 200, Compatible (747600 + i.val) →
    (table.lookup (747600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3738 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 747600 747800 :=
  FiniteIntervals.of_fin 747600 200 complete_chunk3738

lemma complete_chunk3739 : ∀ i : Fin 200, Compatible (747800 + i.val) →
    (table.lookup (747800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3739 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 747800 748000 :=
  FiniteIntervals.of_fin 747800 200 complete_chunk3739

#print axioms interval_chunk3730
end Erdos184Work.PureFiveFilter4
