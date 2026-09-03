import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2620 : ∀ i : Fin 200, Compatible (524000 + i.val) →
    (table.lookup (524000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2620 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 524000 524200 :=
  FiniteIntervals.of_fin 524000 200 complete_chunk2620

lemma complete_chunk2621 : ∀ i : Fin 200, Compatible (524200 + i.val) →
    (table.lookup (524200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2621 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 524200 524400 :=
  FiniteIntervals.of_fin 524200 200 complete_chunk2621

lemma complete_chunk2622 : ∀ i : Fin 200, Compatible (524400 + i.val) →
    (table.lookup (524400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2622 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 524400 524600 :=
  FiniteIntervals.of_fin 524400 200 complete_chunk2622

lemma complete_chunk2623 : ∀ i : Fin 200, Compatible (524600 + i.val) →
    (table.lookup (524600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2623 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 524600 524800 :=
  FiniteIntervals.of_fin 524600 200 complete_chunk2623

lemma complete_chunk2624 : ∀ i : Fin 200, Compatible (524800 + i.val) →
    (table.lookup (524800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2624 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 524800 525000 :=
  FiniteIntervals.of_fin 524800 200 complete_chunk2624

lemma complete_chunk2625 : ∀ i : Fin 200, Compatible (525000 + i.val) →
    (table.lookup (525000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2625 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 525000 525200 :=
  FiniteIntervals.of_fin 525000 200 complete_chunk2625

lemma complete_chunk2626 : ∀ i : Fin 200, Compatible (525200 + i.val) →
    (table.lookup (525200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2626 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 525200 525400 :=
  FiniteIntervals.of_fin 525200 200 complete_chunk2626

lemma complete_chunk2627 : ∀ i : Fin 200, Compatible (525400 + i.val) →
    (table.lookup (525400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2627 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 525400 525600 :=
  FiniteIntervals.of_fin 525400 200 complete_chunk2627

lemma complete_chunk2628 : ∀ i : Fin 200, Compatible (525600 + i.val) →
    (table.lookup (525600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2628 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 525600 525800 :=
  FiniteIntervals.of_fin 525600 200 complete_chunk2628

lemma complete_chunk2629 : ∀ i : Fin 200, Compatible (525800 + i.val) →
    (table.lookup (525800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2629 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 525800 526000 :=
  FiniteIntervals.of_fin 525800 200 complete_chunk2629

#print axioms interval_chunk2620
end Erdos184Work.PureFiveFilter4
