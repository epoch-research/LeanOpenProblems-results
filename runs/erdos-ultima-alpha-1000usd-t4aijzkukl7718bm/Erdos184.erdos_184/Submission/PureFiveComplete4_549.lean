import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5490 : ∀ i : Fin 200, Compatible (1098000 + i.val) →
    (table.lookup (1098000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5490 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1098000 1098200 :=
  FiniteIntervals.of_fin 1098000 200 complete_chunk5490

lemma complete_chunk5491 : ∀ i : Fin 200, Compatible (1098200 + i.val) →
    (table.lookup (1098200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5491 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1098200 1098400 :=
  FiniteIntervals.of_fin 1098200 200 complete_chunk5491

lemma complete_chunk5492 : ∀ i : Fin 200, Compatible (1098400 + i.val) →
    (table.lookup (1098400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5492 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1098400 1098600 :=
  FiniteIntervals.of_fin 1098400 200 complete_chunk5492

lemma complete_chunk5493 : ∀ i : Fin 200, Compatible (1098600 + i.val) →
    (table.lookup (1098600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5493 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1098600 1098800 :=
  FiniteIntervals.of_fin 1098600 200 complete_chunk5493

lemma complete_chunk5494 : ∀ i : Fin 200, Compatible (1098800 + i.val) →
    (table.lookup (1098800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5494 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1098800 1099000 :=
  FiniteIntervals.of_fin 1098800 200 complete_chunk5494

lemma complete_chunk5495 : ∀ i : Fin 200, Compatible (1099000 + i.val) →
    (table.lookup (1099000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5495 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1099000 1099200 :=
  FiniteIntervals.of_fin 1099000 200 complete_chunk5495

lemma complete_chunk5496 : ∀ i : Fin 200, Compatible (1099200 + i.val) →
    (table.lookup (1099200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5496 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1099200 1099400 :=
  FiniteIntervals.of_fin 1099200 200 complete_chunk5496

lemma complete_chunk5497 : ∀ i : Fin 200, Compatible (1099400 + i.val) →
    (table.lookup (1099400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5497 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1099400 1099600 :=
  FiniteIntervals.of_fin 1099400 200 complete_chunk5497

lemma complete_chunk5498 : ∀ i : Fin 200, Compatible (1099600 + i.val) →
    (table.lookup (1099600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5498 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1099600 1099800 :=
  FiniteIntervals.of_fin 1099600 200 complete_chunk5498

lemma complete_chunk5499 : ∀ i : Fin 200, Compatible (1099800 + i.val) →
    (table.lookup (1099800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5499 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1099800 1100000 :=
  FiniteIntervals.of_fin 1099800 200 complete_chunk5499

#print axioms interval_chunk5490
end Erdos184Work.PureFiveFilter4
