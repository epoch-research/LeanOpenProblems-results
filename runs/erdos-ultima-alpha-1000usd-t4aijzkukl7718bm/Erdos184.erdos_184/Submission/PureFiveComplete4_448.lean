import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4480 : ∀ i : Fin 200, Compatible (896000 + i.val) →
    (table.lookup (896000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4480 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 896000 896200 :=
  FiniteIntervals.of_fin 896000 200 complete_chunk4480

lemma complete_chunk4481 : ∀ i : Fin 200, Compatible (896200 + i.val) →
    (table.lookup (896200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4481 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 896200 896400 :=
  FiniteIntervals.of_fin 896200 200 complete_chunk4481

lemma complete_chunk4482 : ∀ i : Fin 200, Compatible (896400 + i.val) →
    (table.lookup (896400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4482 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 896400 896600 :=
  FiniteIntervals.of_fin 896400 200 complete_chunk4482

lemma complete_chunk4483 : ∀ i : Fin 200, Compatible (896600 + i.val) →
    (table.lookup (896600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4483 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 896600 896800 :=
  FiniteIntervals.of_fin 896600 200 complete_chunk4483

lemma complete_chunk4484 : ∀ i : Fin 200, Compatible (896800 + i.val) →
    (table.lookup (896800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4484 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 896800 897000 :=
  FiniteIntervals.of_fin 896800 200 complete_chunk4484

lemma complete_chunk4485 : ∀ i : Fin 200, Compatible (897000 + i.val) →
    (table.lookup (897000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4485 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 897000 897200 :=
  FiniteIntervals.of_fin 897000 200 complete_chunk4485

lemma complete_chunk4486 : ∀ i : Fin 200, Compatible (897200 + i.val) →
    (table.lookup (897200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4486 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 897200 897400 :=
  FiniteIntervals.of_fin 897200 200 complete_chunk4486

lemma complete_chunk4487 : ∀ i : Fin 200, Compatible (897400 + i.val) →
    (table.lookup (897400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4487 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 897400 897600 :=
  FiniteIntervals.of_fin 897400 200 complete_chunk4487

lemma complete_chunk4488 : ∀ i : Fin 200, Compatible (897600 + i.val) →
    (table.lookup (897600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4488 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 897600 897800 :=
  FiniteIntervals.of_fin 897600 200 complete_chunk4488

lemma complete_chunk4489 : ∀ i : Fin 200, Compatible (897800 + i.val) →
    (table.lookup (897800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4489 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 897800 898000 :=
  FiniteIntervals.of_fin 897800 200 complete_chunk4489

#print axioms interval_chunk4480
end Erdos184Work.PureFiveFilter4
