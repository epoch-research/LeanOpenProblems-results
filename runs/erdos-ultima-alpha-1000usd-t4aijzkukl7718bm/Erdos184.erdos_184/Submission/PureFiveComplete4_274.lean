import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2740 : ∀ i : Fin 200, Compatible (548000 + i.val) →
    (table.lookup (548000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2740 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 548000 548200 :=
  FiniteIntervals.of_fin 548000 200 complete_chunk2740

lemma complete_chunk2741 : ∀ i : Fin 200, Compatible (548200 + i.val) →
    (table.lookup (548200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2741 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 548200 548400 :=
  FiniteIntervals.of_fin 548200 200 complete_chunk2741

lemma complete_chunk2742 : ∀ i : Fin 200, Compatible (548400 + i.val) →
    (table.lookup (548400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2742 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 548400 548600 :=
  FiniteIntervals.of_fin 548400 200 complete_chunk2742

lemma complete_chunk2743 : ∀ i : Fin 200, Compatible (548600 + i.val) →
    (table.lookup (548600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2743 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 548600 548800 :=
  FiniteIntervals.of_fin 548600 200 complete_chunk2743

lemma complete_chunk2744 : ∀ i : Fin 200, Compatible (548800 + i.val) →
    (table.lookup (548800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2744 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 548800 549000 :=
  FiniteIntervals.of_fin 548800 200 complete_chunk2744

lemma complete_chunk2745 : ∀ i : Fin 200, Compatible (549000 + i.val) →
    (table.lookup (549000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2745 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 549000 549200 :=
  FiniteIntervals.of_fin 549000 200 complete_chunk2745

lemma complete_chunk2746 : ∀ i : Fin 200, Compatible (549200 + i.val) →
    (table.lookup (549200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2746 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 549200 549400 :=
  FiniteIntervals.of_fin 549200 200 complete_chunk2746

lemma complete_chunk2747 : ∀ i : Fin 200, Compatible (549400 + i.val) →
    (table.lookup (549400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2747 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 549400 549600 :=
  FiniteIntervals.of_fin 549400 200 complete_chunk2747

lemma complete_chunk2748 : ∀ i : Fin 200, Compatible (549600 + i.val) →
    (table.lookup (549600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2748 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 549600 549800 :=
  FiniteIntervals.of_fin 549600 200 complete_chunk2748

lemma complete_chunk2749 : ∀ i : Fin 200, Compatible (549800 + i.val) →
    (table.lookup (549800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2749 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 549800 550000 :=
  FiniteIntervals.of_fin 549800 200 complete_chunk2749

#print axioms interval_chunk2740
end Erdos184Work.PureFiveFilter4
