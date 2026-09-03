import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5680 : ∀ i : Fin 200, Compatible (1136000 + i.val) →
    (table.lookup (1136000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5680 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1136000 1136200 :=
  FiniteIntervals.of_fin 1136000 200 complete_chunk5680

lemma complete_chunk5681 : ∀ i : Fin 200, Compatible (1136200 + i.val) →
    (table.lookup (1136200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5681 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1136200 1136400 :=
  FiniteIntervals.of_fin 1136200 200 complete_chunk5681

lemma complete_chunk5682 : ∀ i : Fin 200, Compatible (1136400 + i.val) →
    (table.lookup (1136400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5682 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1136400 1136600 :=
  FiniteIntervals.of_fin 1136400 200 complete_chunk5682

lemma complete_chunk5683 : ∀ i : Fin 200, Compatible (1136600 + i.val) →
    (table.lookup (1136600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5683 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1136600 1136800 :=
  FiniteIntervals.of_fin 1136600 200 complete_chunk5683

lemma complete_chunk5684 : ∀ i : Fin 200, Compatible (1136800 + i.val) →
    (table.lookup (1136800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5684 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1136800 1137000 :=
  FiniteIntervals.of_fin 1136800 200 complete_chunk5684

lemma complete_chunk5685 : ∀ i : Fin 200, Compatible (1137000 + i.val) →
    (table.lookup (1137000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5685 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1137000 1137200 :=
  FiniteIntervals.of_fin 1137000 200 complete_chunk5685

lemma complete_chunk5686 : ∀ i : Fin 200, Compatible (1137200 + i.val) →
    (table.lookup (1137200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5686 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1137200 1137400 :=
  FiniteIntervals.of_fin 1137200 200 complete_chunk5686

lemma complete_chunk5687 : ∀ i : Fin 200, Compatible (1137400 + i.val) →
    (table.lookup (1137400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5687 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1137400 1137600 :=
  FiniteIntervals.of_fin 1137400 200 complete_chunk5687

lemma complete_chunk5688 : ∀ i : Fin 200, Compatible (1137600 + i.val) →
    (table.lookup (1137600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5688 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1137600 1137800 :=
  FiniteIntervals.of_fin 1137600 200 complete_chunk5688

lemma complete_chunk5689 : ∀ i : Fin 200, Compatible (1137800 + i.val) →
    (table.lookup (1137800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5689 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1137800 1138000 :=
  FiniteIntervals.of_fin 1137800 200 complete_chunk5689

#print axioms interval_chunk5680
end Erdos184Work.PureFiveFilter4
