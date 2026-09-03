import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2630 : ∀ i : Fin 200, Compatible (526000 + i.val) →
    (table.lookup (526000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2630 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 526000 526200 :=
  FiniteIntervals.of_fin 526000 200 complete_chunk2630

lemma complete_chunk2631 : ∀ i : Fin 200, Compatible (526200 + i.val) →
    (table.lookup (526200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2631 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 526200 526400 :=
  FiniteIntervals.of_fin 526200 200 complete_chunk2631

lemma complete_chunk2632 : ∀ i : Fin 200, Compatible (526400 + i.val) →
    (table.lookup (526400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2632 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 526400 526600 :=
  FiniteIntervals.of_fin 526400 200 complete_chunk2632

lemma complete_chunk2633 : ∀ i : Fin 200, Compatible (526600 + i.val) →
    (table.lookup (526600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2633 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 526600 526800 :=
  FiniteIntervals.of_fin 526600 200 complete_chunk2633

lemma complete_chunk2634 : ∀ i : Fin 200, Compatible (526800 + i.val) →
    (table.lookup (526800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2634 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 526800 527000 :=
  FiniteIntervals.of_fin 526800 200 complete_chunk2634

lemma complete_chunk2635 : ∀ i : Fin 200, Compatible (527000 + i.val) →
    (table.lookup (527000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2635 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 527000 527200 :=
  FiniteIntervals.of_fin 527000 200 complete_chunk2635

lemma complete_chunk2636 : ∀ i : Fin 200, Compatible (527200 + i.val) →
    (table.lookup (527200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2636 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 527200 527400 :=
  FiniteIntervals.of_fin 527200 200 complete_chunk2636

lemma complete_chunk2637 : ∀ i : Fin 200, Compatible (527400 + i.val) →
    (table.lookup (527400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2637 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 527400 527600 :=
  FiniteIntervals.of_fin 527400 200 complete_chunk2637

lemma complete_chunk2638 : ∀ i : Fin 200, Compatible (527600 + i.val) →
    (table.lookup (527600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2638 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 527600 527800 :=
  FiniteIntervals.of_fin 527600 200 complete_chunk2638

lemma complete_chunk2639 : ∀ i : Fin 200, Compatible (527800 + i.val) →
    (table.lookup (527800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2639 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 527800 528000 :=
  FiniteIntervals.of_fin 527800 200 complete_chunk2639

#print axioms interval_chunk2630
end Erdos184Work.PureFiveFilter4
