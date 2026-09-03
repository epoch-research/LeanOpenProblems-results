import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2590 : ∀ i : Fin 200, Compatible (518000 + i.val) →
    (table.lookup (518000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2590 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 518000 518200 :=
  FiniteIntervals.of_fin 518000 200 complete_chunk2590

lemma complete_chunk2591 : ∀ i : Fin 200, Compatible (518200 + i.val) →
    (table.lookup (518200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2591 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 518200 518400 :=
  FiniteIntervals.of_fin 518200 200 complete_chunk2591

lemma complete_chunk2592 : ∀ i : Fin 200, Compatible (518400 + i.val) →
    (table.lookup (518400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2592 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 518400 518600 :=
  FiniteIntervals.of_fin 518400 200 complete_chunk2592

lemma complete_chunk2593 : ∀ i : Fin 200, Compatible (518600 + i.val) →
    (table.lookup (518600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2593 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 518600 518800 :=
  FiniteIntervals.of_fin 518600 200 complete_chunk2593

lemma complete_chunk2594 : ∀ i : Fin 200, Compatible (518800 + i.val) →
    (table.lookup (518800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2594 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 518800 519000 :=
  FiniteIntervals.of_fin 518800 200 complete_chunk2594

lemma complete_chunk2595 : ∀ i : Fin 200, Compatible (519000 + i.val) →
    (table.lookup (519000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2595 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 519000 519200 :=
  FiniteIntervals.of_fin 519000 200 complete_chunk2595

lemma complete_chunk2596 : ∀ i : Fin 200, Compatible (519200 + i.val) →
    (table.lookup (519200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2596 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 519200 519400 :=
  FiniteIntervals.of_fin 519200 200 complete_chunk2596

lemma complete_chunk2597 : ∀ i : Fin 200, Compatible (519400 + i.val) →
    (table.lookup (519400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2597 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 519400 519600 :=
  FiniteIntervals.of_fin 519400 200 complete_chunk2597

lemma complete_chunk2598 : ∀ i : Fin 200, Compatible (519600 + i.val) →
    (table.lookup (519600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2598 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 519600 519800 :=
  FiniteIntervals.of_fin 519600 200 complete_chunk2598

lemma complete_chunk2599 : ∀ i : Fin 200, Compatible (519800 + i.val) →
    (table.lookup (519800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2599 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 519800 520000 :=
  FiniteIntervals.of_fin 519800 200 complete_chunk2599

#print axioms interval_chunk2590
end Erdos184Work.PureFiveFilter4
