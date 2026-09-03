import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4470 : ∀ i : Fin 200, Compatible (894000 + i.val) →
    (table.lookup (894000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4470 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 894000 894200 :=
  FiniteIntervals.of_fin 894000 200 complete_chunk4470

lemma complete_chunk4471 : ∀ i : Fin 200, Compatible (894200 + i.val) →
    (table.lookup (894200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4471 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 894200 894400 :=
  FiniteIntervals.of_fin 894200 200 complete_chunk4471

lemma complete_chunk4472 : ∀ i : Fin 200, Compatible (894400 + i.val) →
    (table.lookup (894400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4472 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 894400 894600 :=
  FiniteIntervals.of_fin 894400 200 complete_chunk4472

lemma complete_chunk4473 : ∀ i : Fin 200, Compatible (894600 + i.val) →
    (table.lookup (894600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4473 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 894600 894800 :=
  FiniteIntervals.of_fin 894600 200 complete_chunk4473

lemma complete_chunk4474 : ∀ i : Fin 200, Compatible (894800 + i.val) →
    (table.lookup (894800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4474 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 894800 895000 :=
  FiniteIntervals.of_fin 894800 200 complete_chunk4474

lemma complete_chunk4475 : ∀ i : Fin 200, Compatible (895000 + i.val) →
    (table.lookup (895000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4475 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 895000 895200 :=
  FiniteIntervals.of_fin 895000 200 complete_chunk4475

lemma complete_chunk4476 : ∀ i : Fin 200, Compatible (895200 + i.val) →
    (table.lookup (895200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4476 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 895200 895400 :=
  FiniteIntervals.of_fin 895200 200 complete_chunk4476

lemma complete_chunk4477 : ∀ i : Fin 200, Compatible (895400 + i.val) →
    (table.lookup (895400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4477 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 895400 895600 :=
  FiniteIntervals.of_fin 895400 200 complete_chunk4477

lemma complete_chunk4478 : ∀ i : Fin 200, Compatible (895600 + i.val) →
    (table.lookup (895600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4478 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 895600 895800 :=
  FiniteIntervals.of_fin 895600 200 complete_chunk4478

lemma complete_chunk4479 : ∀ i : Fin 200, Compatible (895800 + i.val) →
    (table.lookup (895800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4479 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 895800 896000 :=
  FiniteIntervals.of_fin 895800 200 complete_chunk4479

#print axioms interval_chunk4470
end Erdos184Work.PureFiveFilter4
