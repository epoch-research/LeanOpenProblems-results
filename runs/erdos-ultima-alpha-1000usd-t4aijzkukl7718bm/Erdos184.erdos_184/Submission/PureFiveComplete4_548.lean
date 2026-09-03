import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5480 : ∀ i : Fin 200, Compatible (1096000 + i.val) →
    (table.lookup (1096000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5480 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1096000 1096200 :=
  FiniteIntervals.of_fin 1096000 200 complete_chunk5480

lemma complete_chunk5481 : ∀ i : Fin 200, Compatible (1096200 + i.val) →
    (table.lookup (1096200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5481 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1096200 1096400 :=
  FiniteIntervals.of_fin 1096200 200 complete_chunk5481

lemma complete_chunk5482 : ∀ i : Fin 200, Compatible (1096400 + i.val) →
    (table.lookup (1096400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5482 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1096400 1096600 :=
  FiniteIntervals.of_fin 1096400 200 complete_chunk5482

lemma complete_chunk5483 : ∀ i : Fin 200, Compatible (1096600 + i.val) →
    (table.lookup (1096600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5483 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1096600 1096800 :=
  FiniteIntervals.of_fin 1096600 200 complete_chunk5483

lemma complete_chunk5484 : ∀ i : Fin 200, Compatible (1096800 + i.val) →
    (table.lookup (1096800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5484 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1096800 1097000 :=
  FiniteIntervals.of_fin 1096800 200 complete_chunk5484

lemma complete_chunk5485 : ∀ i : Fin 200, Compatible (1097000 + i.val) →
    (table.lookup (1097000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5485 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1097000 1097200 :=
  FiniteIntervals.of_fin 1097000 200 complete_chunk5485

lemma complete_chunk5486 : ∀ i : Fin 200, Compatible (1097200 + i.val) →
    (table.lookup (1097200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5486 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1097200 1097400 :=
  FiniteIntervals.of_fin 1097200 200 complete_chunk5486

lemma complete_chunk5487 : ∀ i : Fin 200, Compatible (1097400 + i.val) →
    (table.lookup (1097400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5487 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1097400 1097600 :=
  FiniteIntervals.of_fin 1097400 200 complete_chunk5487

lemma complete_chunk5488 : ∀ i : Fin 200, Compatible (1097600 + i.val) →
    (table.lookup (1097600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5488 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1097600 1097800 :=
  FiniteIntervals.of_fin 1097600 200 complete_chunk5488

lemma complete_chunk5489 : ∀ i : Fin 200, Compatible (1097800 + i.val) →
    (table.lookup (1097800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5489 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1097800 1098000 :=
  FiniteIntervals.of_fin 1097800 200 complete_chunk5489

#print axioms interval_chunk5480
end Erdos184Work.PureFiveFilter4
