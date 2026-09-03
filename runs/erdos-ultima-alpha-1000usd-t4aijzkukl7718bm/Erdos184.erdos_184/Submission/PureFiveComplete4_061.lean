import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk610 : ∀ i : Fin 200, Compatible (122000 + i.val) →
    (table.lookup (122000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk610 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 122000 122200 :=
  FiniteIntervals.of_fin 122000 200 complete_chunk610

lemma complete_chunk611 : ∀ i : Fin 200, Compatible (122200 + i.val) →
    (table.lookup (122200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk611 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 122200 122400 :=
  FiniteIntervals.of_fin 122200 200 complete_chunk611

lemma complete_chunk612 : ∀ i : Fin 200, Compatible (122400 + i.val) →
    (table.lookup (122400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk612 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 122400 122600 :=
  FiniteIntervals.of_fin 122400 200 complete_chunk612

lemma complete_chunk613 : ∀ i : Fin 200, Compatible (122600 + i.val) →
    (table.lookup (122600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk613 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 122600 122800 :=
  FiniteIntervals.of_fin 122600 200 complete_chunk613

lemma complete_chunk614 : ∀ i : Fin 200, Compatible (122800 + i.val) →
    (table.lookup (122800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk614 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 122800 123000 :=
  FiniteIntervals.of_fin 122800 200 complete_chunk614

lemma complete_chunk615 : ∀ i : Fin 200, Compatible (123000 + i.val) →
    (table.lookup (123000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk615 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 123000 123200 :=
  FiniteIntervals.of_fin 123000 200 complete_chunk615

lemma complete_chunk616 : ∀ i : Fin 200, Compatible (123200 + i.val) →
    (table.lookup (123200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk616 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 123200 123400 :=
  FiniteIntervals.of_fin 123200 200 complete_chunk616

lemma complete_chunk617 : ∀ i : Fin 200, Compatible (123400 + i.val) →
    (table.lookup (123400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk617 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 123400 123600 :=
  FiniteIntervals.of_fin 123400 200 complete_chunk617

lemma complete_chunk618 : ∀ i : Fin 200, Compatible (123600 + i.val) →
    (table.lookup (123600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk618 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 123600 123800 :=
  FiniteIntervals.of_fin 123600 200 complete_chunk618

lemma complete_chunk619 : ∀ i : Fin 200, Compatible (123800 + i.val) →
    (table.lookup (123800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk619 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 123800 124000 :=
  FiniteIntervals.of_fin 123800 200 complete_chunk619

#print axioms interval_chunk610
end Erdos184Work.PureFiveFilter4
