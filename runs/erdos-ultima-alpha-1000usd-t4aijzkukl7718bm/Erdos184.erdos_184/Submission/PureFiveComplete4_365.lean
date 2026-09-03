import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3650 : ∀ i : Fin 200, Compatible (730000 + i.val) →
    (table.lookup (730000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3650 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 730000 730200 :=
  FiniteIntervals.of_fin 730000 200 complete_chunk3650

lemma complete_chunk3651 : ∀ i : Fin 200, Compatible (730200 + i.val) →
    (table.lookup (730200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3651 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 730200 730400 :=
  FiniteIntervals.of_fin 730200 200 complete_chunk3651

lemma complete_chunk3652 : ∀ i : Fin 200, Compatible (730400 + i.val) →
    (table.lookup (730400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3652 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 730400 730600 :=
  FiniteIntervals.of_fin 730400 200 complete_chunk3652

lemma complete_chunk3653 : ∀ i : Fin 200, Compatible (730600 + i.val) →
    (table.lookup (730600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3653 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 730600 730800 :=
  FiniteIntervals.of_fin 730600 200 complete_chunk3653

lemma complete_chunk3654 : ∀ i : Fin 200, Compatible (730800 + i.val) →
    (table.lookup (730800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3654 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 730800 731000 :=
  FiniteIntervals.of_fin 730800 200 complete_chunk3654

lemma complete_chunk3655 : ∀ i : Fin 200, Compatible (731000 + i.val) →
    (table.lookup (731000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3655 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 731000 731200 :=
  FiniteIntervals.of_fin 731000 200 complete_chunk3655

lemma complete_chunk3656 : ∀ i : Fin 200, Compatible (731200 + i.val) →
    (table.lookup (731200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3656 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 731200 731400 :=
  FiniteIntervals.of_fin 731200 200 complete_chunk3656

lemma complete_chunk3657 : ∀ i : Fin 200, Compatible (731400 + i.val) →
    (table.lookup (731400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3657 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 731400 731600 :=
  FiniteIntervals.of_fin 731400 200 complete_chunk3657

lemma complete_chunk3658 : ∀ i : Fin 200, Compatible (731600 + i.val) →
    (table.lookup (731600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3658 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 731600 731800 :=
  FiniteIntervals.of_fin 731600 200 complete_chunk3658

lemma complete_chunk3659 : ∀ i : Fin 200, Compatible (731800 + i.val) →
    (table.lookup (731800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3659 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 731800 732000 :=
  FiniteIntervals.of_fin 731800 200 complete_chunk3659

#print axioms interval_chunk3650
end Erdos184Work.PureFiveFilter4
