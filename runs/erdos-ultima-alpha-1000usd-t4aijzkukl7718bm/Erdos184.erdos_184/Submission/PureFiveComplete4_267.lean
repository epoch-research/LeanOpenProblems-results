import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2670 : ∀ i : Fin 200, Compatible (534000 + i.val) →
    (table.lookup (534000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2670 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 534000 534200 :=
  FiniteIntervals.of_fin 534000 200 complete_chunk2670

lemma complete_chunk2671 : ∀ i : Fin 200, Compatible (534200 + i.val) →
    (table.lookup (534200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2671 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 534200 534400 :=
  FiniteIntervals.of_fin 534200 200 complete_chunk2671

lemma complete_chunk2672 : ∀ i : Fin 200, Compatible (534400 + i.val) →
    (table.lookup (534400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2672 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 534400 534600 :=
  FiniteIntervals.of_fin 534400 200 complete_chunk2672

lemma complete_chunk2673 : ∀ i : Fin 200, Compatible (534600 + i.val) →
    (table.lookup (534600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2673 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 534600 534800 :=
  FiniteIntervals.of_fin 534600 200 complete_chunk2673

lemma complete_chunk2674 : ∀ i : Fin 200, Compatible (534800 + i.val) →
    (table.lookup (534800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2674 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 534800 535000 :=
  FiniteIntervals.of_fin 534800 200 complete_chunk2674

lemma complete_chunk2675 : ∀ i : Fin 200, Compatible (535000 + i.val) →
    (table.lookup (535000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2675 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 535000 535200 :=
  FiniteIntervals.of_fin 535000 200 complete_chunk2675

lemma complete_chunk2676 : ∀ i : Fin 200, Compatible (535200 + i.val) →
    (table.lookup (535200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2676 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 535200 535400 :=
  FiniteIntervals.of_fin 535200 200 complete_chunk2676

lemma complete_chunk2677 : ∀ i : Fin 200, Compatible (535400 + i.val) →
    (table.lookup (535400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2677 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 535400 535600 :=
  FiniteIntervals.of_fin 535400 200 complete_chunk2677

lemma complete_chunk2678 : ∀ i : Fin 200, Compatible (535600 + i.val) →
    (table.lookup (535600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2678 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 535600 535800 :=
  FiniteIntervals.of_fin 535600 200 complete_chunk2678

lemma complete_chunk2679 : ∀ i : Fin 200, Compatible (535800 + i.val) →
    (table.lookup (535800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2679 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 535800 536000 :=
  FiniteIntervals.of_fin 535800 200 complete_chunk2679

#print axioms interval_chunk2670
end Erdos184Work.PureFiveFilter4
