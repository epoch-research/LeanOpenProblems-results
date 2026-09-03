import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4640 : ∀ i : Fin 200, Compatible (928000 + i.val) →
    (table.lookup (928000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4640 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 928000 928200 :=
  FiniteIntervals.of_fin 928000 200 complete_chunk4640

lemma complete_chunk4641 : ∀ i : Fin 200, Compatible (928200 + i.val) →
    (table.lookup (928200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4641 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 928200 928400 :=
  FiniteIntervals.of_fin 928200 200 complete_chunk4641

lemma complete_chunk4642 : ∀ i : Fin 200, Compatible (928400 + i.val) →
    (table.lookup (928400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4642 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 928400 928600 :=
  FiniteIntervals.of_fin 928400 200 complete_chunk4642

lemma complete_chunk4643 : ∀ i : Fin 200, Compatible (928600 + i.val) →
    (table.lookup (928600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4643 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 928600 928800 :=
  FiniteIntervals.of_fin 928600 200 complete_chunk4643

lemma complete_chunk4644 : ∀ i : Fin 200, Compatible (928800 + i.val) →
    (table.lookup (928800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4644 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 928800 929000 :=
  FiniteIntervals.of_fin 928800 200 complete_chunk4644

lemma complete_chunk4645 : ∀ i : Fin 200, Compatible (929000 + i.val) →
    (table.lookup (929000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4645 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 929000 929200 :=
  FiniteIntervals.of_fin 929000 200 complete_chunk4645

lemma complete_chunk4646 : ∀ i : Fin 200, Compatible (929200 + i.val) →
    (table.lookup (929200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4646 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 929200 929400 :=
  FiniteIntervals.of_fin 929200 200 complete_chunk4646

lemma complete_chunk4647 : ∀ i : Fin 200, Compatible (929400 + i.val) →
    (table.lookup (929400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4647 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 929400 929600 :=
  FiniteIntervals.of_fin 929400 200 complete_chunk4647

lemma complete_chunk4648 : ∀ i : Fin 200, Compatible (929600 + i.val) →
    (table.lookup (929600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4648 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 929600 929800 :=
  FiniteIntervals.of_fin 929600 200 complete_chunk4648

lemma complete_chunk4649 : ∀ i : Fin 200, Compatible (929800 + i.val) →
    (table.lookup (929800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4649 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 929800 930000 :=
  FiniteIntervals.of_fin 929800 200 complete_chunk4649

#print axioms interval_chunk4640
end Erdos184Work.PureFiveFilter4
