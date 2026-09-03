import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4400 : ∀ i : Fin 200, Compatible (880000 + i.val) →
    (table.lookup (880000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4400 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 880000 880200 :=
  FiniteIntervals.of_fin 880000 200 complete_chunk4400

lemma complete_chunk4401 : ∀ i : Fin 200, Compatible (880200 + i.val) →
    (table.lookup (880200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4401 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 880200 880400 :=
  FiniteIntervals.of_fin 880200 200 complete_chunk4401

lemma complete_chunk4402 : ∀ i : Fin 200, Compatible (880400 + i.val) →
    (table.lookup (880400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4402 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 880400 880600 :=
  FiniteIntervals.of_fin 880400 200 complete_chunk4402

lemma complete_chunk4403 : ∀ i : Fin 200, Compatible (880600 + i.val) →
    (table.lookup (880600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4403 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 880600 880800 :=
  FiniteIntervals.of_fin 880600 200 complete_chunk4403

lemma complete_chunk4404 : ∀ i : Fin 200, Compatible (880800 + i.val) →
    (table.lookup (880800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4404 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 880800 881000 :=
  FiniteIntervals.of_fin 880800 200 complete_chunk4404

lemma complete_chunk4405 : ∀ i : Fin 200, Compatible (881000 + i.val) →
    (table.lookup (881000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4405 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 881000 881200 :=
  FiniteIntervals.of_fin 881000 200 complete_chunk4405

lemma complete_chunk4406 : ∀ i : Fin 200, Compatible (881200 + i.val) →
    (table.lookup (881200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4406 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 881200 881400 :=
  FiniteIntervals.of_fin 881200 200 complete_chunk4406

lemma complete_chunk4407 : ∀ i : Fin 200, Compatible (881400 + i.val) →
    (table.lookup (881400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4407 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 881400 881600 :=
  FiniteIntervals.of_fin 881400 200 complete_chunk4407

lemma complete_chunk4408 : ∀ i : Fin 200, Compatible (881600 + i.val) →
    (table.lookup (881600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4408 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 881600 881800 :=
  FiniteIntervals.of_fin 881600 200 complete_chunk4408

lemma complete_chunk4409 : ∀ i : Fin 200, Compatible (881800 + i.val) →
    (table.lookup (881800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4409 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 881800 882000 :=
  FiniteIntervals.of_fin 881800 200 complete_chunk4409

#print axioms interval_chunk4400
end Erdos184Work.PureFiveFilter4
