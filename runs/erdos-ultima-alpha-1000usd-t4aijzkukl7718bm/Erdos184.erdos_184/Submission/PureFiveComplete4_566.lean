import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5660 : ∀ i : Fin 200, Compatible (1132000 + i.val) →
    (table.lookup (1132000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5660 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1132000 1132200 :=
  FiniteIntervals.of_fin 1132000 200 complete_chunk5660

lemma complete_chunk5661 : ∀ i : Fin 200, Compatible (1132200 + i.val) →
    (table.lookup (1132200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5661 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1132200 1132400 :=
  FiniteIntervals.of_fin 1132200 200 complete_chunk5661

lemma complete_chunk5662 : ∀ i : Fin 200, Compatible (1132400 + i.val) →
    (table.lookup (1132400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5662 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1132400 1132600 :=
  FiniteIntervals.of_fin 1132400 200 complete_chunk5662

lemma complete_chunk5663 : ∀ i : Fin 200, Compatible (1132600 + i.val) →
    (table.lookup (1132600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5663 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1132600 1132800 :=
  FiniteIntervals.of_fin 1132600 200 complete_chunk5663

lemma complete_chunk5664 : ∀ i : Fin 200, Compatible (1132800 + i.val) →
    (table.lookup (1132800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5664 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1132800 1133000 :=
  FiniteIntervals.of_fin 1132800 200 complete_chunk5664

lemma complete_chunk5665 : ∀ i : Fin 200, Compatible (1133000 + i.val) →
    (table.lookup (1133000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5665 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1133000 1133200 :=
  FiniteIntervals.of_fin 1133000 200 complete_chunk5665

lemma complete_chunk5666 : ∀ i : Fin 200, Compatible (1133200 + i.val) →
    (table.lookup (1133200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5666 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1133200 1133400 :=
  FiniteIntervals.of_fin 1133200 200 complete_chunk5666

lemma complete_chunk5667 : ∀ i : Fin 200, Compatible (1133400 + i.val) →
    (table.lookup (1133400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5667 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1133400 1133600 :=
  FiniteIntervals.of_fin 1133400 200 complete_chunk5667

lemma complete_chunk5668 : ∀ i : Fin 200, Compatible (1133600 + i.val) →
    (table.lookup (1133600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5668 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1133600 1133800 :=
  FiniteIntervals.of_fin 1133600 200 complete_chunk5668

lemma complete_chunk5669 : ∀ i : Fin 200, Compatible (1133800 + i.val) →
    (table.lookup (1133800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5669 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1133800 1134000 :=
  FiniteIntervals.of_fin 1133800 200 complete_chunk5669

#print axioms interval_chunk5660
end Erdos184Work.PureFiveFilter4
