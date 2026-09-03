import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5610 : ∀ i : Fin 200, Compatible (1122000 + i.val) →
    (table.lookup (1122000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5610 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1122000 1122200 :=
  FiniteIntervals.of_fin 1122000 200 complete_chunk5610

lemma complete_chunk5611 : ∀ i : Fin 200, Compatible (1122200 + i.val) →
    (table.lookup (1122200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5611 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1122200 1122400 :=
  FiniteIntervals.of_fin 1122200 200 complete_chunk5611

lemma complete_chunk5612 : ∀ i : Fin 200, Compatible (1122400 + i.val) →
    (table.lookup (1122400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5612 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1122400 1122600 :=
  FiniteIntervals.of_fin 1122400 200 complete_chunk5612

lemma complete_chunk5613 : ∀ i : Fin 200, Compatible (1122600 + i.val) →
    (table.lookup (1122600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5613 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1122600 1122800 :=
  FiniteIntervals.of_fin 1122600 200 complete_chunk5613

lemma complete_chunk5614 : ∀ i : Fin 200, Compatible (1122800 + i.val) →
    (table.lookup (1122800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5614 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1122800 1123000 :=
  FiniteIntervals.of_fin 1122800 200 complete_chunk5614

lemma complete_chunk5615 : ∀ i : Fin 200, Compatible (1123000 + i.val) →
    (table.lookup (1123000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5615 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1123000 1123200 :=
  FiniteIntervals.of_fin 1123000 200 complete_chunk5615

lemma complete_chunk5616 : ∀ i : Fin 200, Compatible (1123200 + i.val) →
    (table.lookup (1123200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5616 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1123200 1123400 :=
  FiniteIntervals.of_fin 1123200 200 complete_chunk5616

lemma complete_chunk5617 : ∀ i : Fin 200, Compatible (1123400 + i.val) →
    (table.lookup (1123400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5617 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1123400 1123600 :=
  FiniteIntervals.of_fin 1123400 200 complete_chunk5617

lemma complete_chunk5618 : ∀ i : Fin 200, Compatible (1123600 + i.val) →
    (table.lookup (1123600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5618 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1123600 1123800 :=
  FiniteIntervals.of_fin 1123600 200 complete_chunk5618

lemma complete_chunk5619 : ∀ i : Fin 200, Compatible (1123800 + i.val) →
    (table.lookup (1123800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5619 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1123800 1124000 :=
  FiniteIntervals.of_fin 1123800 200 complete_chunk5619

#print axioms interval_chunk5610
end Erdos184Work.PureFiveFilter4
