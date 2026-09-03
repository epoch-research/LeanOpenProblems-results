import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4700 : ∀ i : Fin 200, Compatible (940000 + i.val) →
    (table.lookup (940000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4700 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 940000 940200 :=
  FiniteIntervals.of_fin 940000 200 complete_chunk4700

lemma complete_chunk4701 : ∀ i : Fin 200, Compatible (940200 + i.val) →
    (table.lookup (940200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4701 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 940200 940400 :=
  FiniteIntervals.of_fin 940200 200 complete_chunk4701

lemma complete_chunk4702 : ∀ i : Fin 200, Compatible (940400 + i.val) →
    (table.lookup (940400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4702 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 940400 940600 :=
  FiniteIntervals.of_fin 940400 200 complete_chunk4702

lemma complete_chunk4703 : ∀ i : Fin 200, Compatible (940600 + i.val) →
    (table.lookup (940600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4703 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 940600 940800 :=
  FiniteIntervals.of_fin 940600 200 complete_chunk4703

lemma complete_chunk4704 : ∀ i : Fin 200, Compatible (940800 + i.val) →
    (table.lookup (940800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4704 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 940800 941000 :=
  FiniteIntervals.of_fin 940800 200 complete_chunk4704

lemma complete_chunk4705 : ∀ i : Fin 200, Compatible (941000 + i.val) →
    (table.lookup (941000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4705 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 941000 941200 :=
  FiniteIntervals.of_fin 941000 200 complete_chunk4705

lemma complete_chunk4706 : ∀ i : Fin 200, Compatible (941200 + i.val) →
    (table.lookup (941200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4706 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 941200 941400 :=
  FiniteIntervals.of_fin 941200 200 complete_chunk4706

lemma complete_chunk4707 : ∀ i : Fin 200, Compatible (941400 + i.val) →
    (table.lookup (941400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4707 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 941400 941600 :=
  FiniteIntervals.of_fin 941400 200 complete_chunk4707

lemma complete_chunk4708 : ∀ i : Fin 200, Compatible (941600 + i.val) →
    (table.lookup (941600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4708 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 941600 941800 :=
  FiniteIntervals.of_fin 941600 200 complete_chunk4708

lemma complete_chunk4709 : ∀ i : Fin 200, Compatible (941800 + i.val) →
    (table.lookup (941800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4709 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 941800 942000 :=
  FiniteIntervals.of_fin 941800 200 complete_chunk4709

#print axioms interval_chunk4700
end Erdos184Work.PureFiveFilter4
