import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk660 : ∀ i : Fin 200, Compatible (132000 + i.val) →
    (table.lookup (132000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk660 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 132000 132200 :=
  FiniteIntervals.of_fin 132000 200 complete_chunk660

lemma complete_chunk661 : ∀ i : Fin 200, Compatible (132200 + i.val) →
    (table.lookup (132200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk661 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 132200 132400 :=
  FiniteIntervals.of_fin 132200 200 complete_chunk661

lemma complete_chunk662 : ∀ i : Fin 200, Compatible (132400 + i.val) →
    (table.lookup (132400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk662 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 132400 132600 :=
  FiniteIntervals.of_fin 132400 200 complete_chunk662

lemma complete_chunk663 : ∀ i : Fin 200, Compatible (132600 + i.val) →
    (table.lookup (132600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk663 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 132600 132800 :=
  FiniteIntervals.of_fin 132600 200 complete_chunk663

lemma complete_chunk664 : ∀ i : Fin 200, Compatible (132800 + i.val) →
    (table.lookup (132800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk664 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 132800 133000 :=
  FiniteIntervals.of_fin 132800 200 complete_chunk664

lemma complete_chunk665 : ∀ i : Fin 200, Compatible (133000 + i.val) →
    (table.lookup (133000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk665 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 133000 133200 :=
  FiniteIntervals.of_fin 133000 200 complete_chunk665

lemma complete_chunk666 : ∀ i : Fin 200, Compatible (133200 + i.val) →
    (table.lookup (133200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk666 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 133200 133400 :=
  FiniteIntervals.of_fin 133200 200 complete_chunk666

lemma complete_chunk667 : ∀ i : Fin 200, Compatible (133400 + i.val) →
    (table.lookup (133400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk667 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 133400 133600 :=
  FiniteIntervals.of_fin 133400 200 complete_chunk667

lemma complete_chunk668 : ∀ i : Fin 200, Compatible (133600 + i.val) →
    (table.lookup (133600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk668 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 133600 133800 :=
  FiniteIntervals.of_fin 133600 200 complete_chunk668

lemma complete_chunk669 : ∀ i : Fin 200, Compatible (133800 + i.val) →
    (table.lookup (133800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk669 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 133800 134000 :=
  FiniteIntervals.of_fin 133800 200 complete_chunk669

#print axioms interval_chunk660
end Erdos184Work.PureFiveFilter4
