import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4450 : ∀ i : Fin 200, Compatible (890000 + i.val) →
    (table.lookup (890000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4450 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 890000 890200 :=
  FiniteIntervals.of_fin 890000 200 complete_chunk4450

lemma complete_chunk4451 : ∀ i : Fin 200, Compatible (890200 + i.val) →
    (table.lookup (890200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4451 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 890200 890400 :=
  FiniteIntervals.of_fin 890200 200 complete_chunk4451

lemma complete_chunk4452 : ∀ i : Fin 200, Compatible (890400 + i.val) →
    (table.lookup (890400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4452 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 890400 890600 :=
  FiniteIntervals.of_fin 890400 200 complete_chunk4452

lemma complete_chunk4453 : ∀ i : Fin 200, Compatible (890600 + i.val) →
    (table.lookup (890600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4453 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 890600 890800 :=
  FiniteIntervals.of_fin 890600 200 complete_chunk4453

lemma complete_chunk4454 : ∀ i : Fin 200, Compatible (890800 + i.val) →
    (table.lookup (890800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4454 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 890800 891000 :=
  FiniteIntervals.of_fin 890800 200 complete_chunk4454

lemma complete_chunk4455 : ∀ i : Fin 200, Compatible (891000 + i.val) →
    (table.lookup (891000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4455 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 891000 891200 :=
  FiniteIntervals.of_fin 891000 200 complete_chunk4455

lemma complete_chunk4456 : ∀ i : Fin 200, Compatible (891200 + i.val) →
    (table.lookup (891200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4456 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 891200 891400 :=
  FiniteIntervals.of_fin 891200 200 complete_chunk4456

lemma complete_chunk4457 : ∀ i : Fin 200, Compatible (891400 + i.val) →
    (table.lookup (891400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4457 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 891400 891600 :=
  FiniteIntervals.of_fin 891400 200 complete_chunk4457

lemma complete_chunk4458 : ∀ i : Fin 200, Compatible (891600 + i.val) →
    (table.lookup (891600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4458 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 891600 891800 :=
  FiniteIntervals.of_fin 891600 200 complete_chunk4458

lemma complete_chunk4459 : ∀ i : Fin 200, Compatible (891800 + i.val) →
    (table.lookup (891800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4459 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 891800 892000 :=
  FiniteIntervals.of_fin 891800 200 complete_chunk4459

#print axioms interval_chunk4450
end Erdos184Work.PureFiveFilter4
