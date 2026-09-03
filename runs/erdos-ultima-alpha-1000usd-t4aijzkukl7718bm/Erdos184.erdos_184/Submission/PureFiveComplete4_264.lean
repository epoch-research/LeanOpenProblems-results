import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2640 : ∀ i : Fin 200, Compatible (528000 + i.val) →
    (table.lookup (528000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2640 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 528000 528200 :=
  FiniteIntervals.of_fin 528000 200 complete_chunk2640

lemma complete_chunk2641 : ∀ i : Fin 200, Compatible (528200 + i.val) →
    (table.lookup (528200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2641 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 528200 528400 :=
  FiniteIntervals.of_fin 528200 200 complete_chunk2641

lemma complete_chunk2642 : ∀ i : Fin 200, Compatible (528400 + i.val) →
    (table.lookup (528400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2642 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 528400 528600 :=
  FiniteIntervals.of_fin 528400 200 complete_chunk2642

lemma complete_chunk2643 : ∀ i : Fin 200, Compatible (528600 + i.val) →
    (table.lookup (528600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2643 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 528600 528800 :=
  FiniteIntervals.of_fin 528600 200 complete_chunk2643

lemma complete_chunk2644 : ∀ i : Fin 200, Compatible (528800 + i.val) →
    (table.lookup (528800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2644 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 528800 529000 :=
  FiniteIntervals.of_fin 528800 200 complete_chunk2644

lemma complete_chunk2645 : ∀ i : Fin 200, Compatible (529000 + i.val) →
    (table.lookup (529000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2645 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 529000 529200 :=
  FiniteIntervals.of_fin 529000 200 complete_chunk2645

lemma complete_chunk2646 : ∀ i : Fin 200, Compatible (529200 + i.val) →
    (table.lookup (529200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2646 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 529200 529400 :=
  FiniteIntervals.of_fin 529200 200 complete_chunk2646

lemma complete_chunk2647 : ∀ i : Fin 200, Compatible (529400 + i.val) →
    (table.lookup (529400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2647 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 529400 529600 :=
  FiniteIntervals.of_fin 529400 200 complete_chunk2647

lemma complete_chunk2648 : ∀ i : Fin 200, Compatible (529600 + i.val) →
    (table.lookup (529600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2648 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 529600 529800 :=
  FiniteIntervals.of_fin 529600 200 complete_chunk2648

lemma complete_chunk2649 : ∀ i : Fin 200, Compatible (529800 + i.val) →
    (table.lookup (529800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2649 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 529800 530000 :=
  FiniteIntervals.of_fin 529800 200 complete_chunk2649

#print axioms interval_chunk2640
end Erdos184Work.PureFiveFilter4
