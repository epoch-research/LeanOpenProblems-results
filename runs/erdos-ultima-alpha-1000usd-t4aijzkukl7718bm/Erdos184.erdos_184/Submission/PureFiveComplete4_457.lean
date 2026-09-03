import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4570 : ∀ i : Fin 200, Compatible (914000 + i.val) →
    (table.lookup (914000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4570 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 914000 914200 :=
  FiniteIntervals.of_fin 914000 200 complete_chunk4570

lemma complete_chunk4571 : ∀ i : Fin 200, Compatible (914200 + i.val) →
    (table.lookup (914200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4571 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 914200 914400 :=
  FiniteIntervals.of_fin 914200 200 complete_chunk4571

lemma complete_chunk4572 : ∀ i : Fin 200, Compatible (914400 + i.val) →
    (table.lookup (914400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4572 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 914400 914600 :=
  FiniteIntervals.of_fin 914400 200 complete_chunk4572

lemma complete_chunk4573 : ∀ i : Fin 200, Compatible (914600 + i.val) →
    (table.lookup (914600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4573 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 914600 914800 :=
  FiniteIntervals.of_fin 914600 200 complete_chunk4573

lemma complete_chunk4574 : ∀ i : Fin 200, Compatible (914800 + i.val) →
    (table.lookup (914800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4574 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 914800 915000 :=
  FiniteIntervals.of_fin 914800 200 complete_chunk4574

lemma complete_chunk4575 : ∀ i : Fin 200, Compatible (915000 + i.val) →
    (table.lookup (915000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4575 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 915000 915200 :=
  FiniteIntervals.of_fin 915000 200 complete_chunk4575

lemma complete_chunk4576 : ∀ i : Fin 200, Compatible (915200 + i.val) →
    (table.lookup (915200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4576 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 915200 915400 :=
  FiniteIntervals.of_fin 915200 200 complete_chunk4576

lemma complete_chunk4577 : ∀ i : Fin 200, Compatible (915400 + i.val) →
    (table.lookup (915400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4577 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 915400 915600 :=
  FiniteIntervals.of_fin 915400 200 complete_chunk4577

lemma complete_chunk4578 : ∀ i : Fin 200, Compatible (915600 + i.val) →
    (table.lookup (915600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4578 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 915600 915800 :=
  FiniteIntervals.of_fin 915600 200 complete_chunk4578

lemma complete_chunk4579 : ∀ i : Fin 200, Compatible (915800 + i.val) →
    (table.lookup (915800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4579 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 915800 916000 :=
  FiniteIntervals.of_fin 915800 200 complete_chunk4579

#print axioms interval_chunk4570
end Erdos184Work.PureFiveFilter4
