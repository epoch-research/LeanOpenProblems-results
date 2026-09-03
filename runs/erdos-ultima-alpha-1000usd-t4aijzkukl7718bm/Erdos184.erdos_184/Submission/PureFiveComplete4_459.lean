import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4590 : ∀ i : Fin 200, Compatible (918000 + i.val) →
    (table.lookup (918000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4590 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 918000 918200 :=
  FiniteIntervals.of_fin 918000 200 complete_chunk4590

lemma complete_chunk4591 : ∀ i : Fin 200, Compatible (918200 + i.val) →
    (table.lookup (918200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4591 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 918200 918400 :=
  FiniteIntervals.of_fin 918200 200 complete_chunk4591

lemma complete_chunk4592 : ∀ i : Fin 200, Compatible (918400 + i.val) →
    (table.lookup (918400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4592 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 918400 918600 :=
  FiniteIntervals.of_fin 918400 200 complete_chunk4592

lemma complete_chunk4593 : ∀ i : Fin 200, Compatible (918600 + i.val) →
    (table.lookup (918600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4593 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 918600 918800 :=
  FiniteIntervals.of_fin 918600 200 complete_chunk4593

lemma complete_chunk4594 : ∀ i : Fin 200, Compatible (918800 + i.val) →
    (table.lookup (918800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4594 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 918800 919000 :=
  FiniteIntervals.of_fin 918800 200 complete_chunk4594

lemma complete_chunk4595 : ∀ i : Fin 200, Compatible (919000 + i.val) →
    (table.lookup (919000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4595 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 919000 919200 :=
  FiniteIntervals.of_fin 919000 200 complete_chunk4595

lemma complete_chunk4596 : ∀ i : Fin 200, Compatible (919200 + i.val) →
    (table.lookup (919200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4596 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 919200 919400 :=
  FiniteIntervals.of_fin 919200 200 complete_chunk4596

lemma complete_chunk4597 : ∀ i : Fin 200, Compatible (919400 + i.val) →
    (table.lookup (919400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4597 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 919400 919600 :=
  FiniteIntervals.of_fin 919400 200 complete_chunk4597

lemma complete_chunk4598 : ∀ i : Fin 200, Compatible (919600 + i.val) →
    (table.lookup (919600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4598 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 919600 919800 :=
  FiniteIntervals.of_fin 919600 200 complete_chunk4598

lemma complete_chunk4599 : ∀ i : Fin 200, Compatible (919800 + i.val) →
    (table.lookup (919800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4599 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 919800 920000 :=
  FiniteIntervals.of_fin 919800 200 complete_chunk4599

#print axioms interval_chunk4590
end Erdos184Work.PureFiveFilter4
