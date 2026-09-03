import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk710 : ∀ i : Fin 200, Compatible (142000 + i.val) →
    (table.lookup (142000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk710 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 142000 142200 :=
  FiniteIntervals.of_fin 142000 200 complete_chunk710

lemma complete_chunk711 : ∀ i : Fin 200, Compatible (142200 + i.val) →
    (table.lookup (142200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk711 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 142200 142400 :=
  FiniteIntervals.of_fin 142200 200 complete_chunk711

lemma complete_chunk712 : ∀ i : Fin 200, Compatible (142400 + i.val) →
    (table.lookup (142400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk712 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 142400 142600 :=
  FiniteIntervals.of_fin 142400 200 complete_chunk712

lemma complete_chunk713 : ∀ i : Fin 200, Compatible (142600 + i.val) →
    (table.lookup (142600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk713 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 142600 142800 :=
  FiniteIntervals.of_fin 142600 200 complete_chunk713

lemma complete_chunk714 : ∀ i : Fin 200, Compatible (142800 + i.val) →
    (table.lookup (142800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk714 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 142800 143000 :=
  FiniteIntervals.of_fin 142800 200 complete_chunk714

lemma complete_chunk715 : ∀ i : Fin 200, Compatible (143000 + i.val) →
    (table.lookup (143000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk715 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 143000 143200 :=
  FiniteIntervals.of_fin 143000 200 complete_chunk715

lemma complete_chunk716 : ∀ i : Fin 200, Compatible (143200 + i.val) →
    (table.lookup (143200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk716 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 143200 143400 :=
  FiniteIntervals.of_fin 143200 200 complete_chunk716

lemma complete_chunk717 : ∀ i : Fin 200, Compatible (143400 + i.val) →
    (table.lookup (143400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk717 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 143400 143600 :=
  FiniteIntervals.of_fin 143400 200 complete_chunk717

lemma complete_chunk718 : ∀ i : Fin 200, Compatible (143600 + i.val) →
    (table.lookup (143600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk718 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 143600 143800 :=
  FiniteIntervals.of_fin 143600 200 complete_chunk718

lemma complete_chunk719 : ∀ i : Fin 200, Compatible (143800 + i.val) →
    (table.lookup (143800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk719 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 143800 144000 :=
  FiniteIntervals.of_fin 143800 200 complete_chunk719

#print axioms interval_chunk710
end Erdos184Work.PureFiveFilter4
