import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4370 : ∀ i : Fin 200, Compatible (874000 + i.val) →
    (table.lookup (874000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4370 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 874000 874200 :=
  FiniteIntervals.of_fin 874000 200 complete_chunk4370

lemma complete_chunk4371 : ∀ i : Fin 200, Compatible (874200 + i.val) →
    (table.lookup (874200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4371 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 874200 874400 :=
  FiniteIntervals.of_fin 874200 200 complete_chunk4371

lemma complete_chunk4372 : ∀ i : Fin 200, Compatible (874400 + i.val) →
    (table.lookup (874400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4372 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 874400 874600 :=
  FiniteIntervals.of_fin 874400 200 complete_chunk4372

lemma complete_chunk4373 : ∀ i : Fin 200, Compatible (874600 + i.val) →
    (table.lookup (874600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4373 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 874600 874800 :=
  FiniteIntervals.of_fin 874600 200 complete_chunk4373

lemma complete_chunk4374 : ∀ i : Fin 200, Compatible (874800 + i.val) →
    (table.lookup (874800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4374 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 874800 875000 :=
  FiniteIntervals.of_fin 874800 200 complete_chunk4374

lemma complete_chunk4375 : ∀ i : Fin 200, Compatible (875000 + i.val) →
    (table.lookup (875000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4375 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 875000 875200 :=
  FiniteIntervals.of_fin 875000 200 complete_chunk4375

lemma complete_chunk4376 : ∀ i : Fin 200, Compatible (875200 + i.val) →
    (table.lookup (875200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4376 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 875200 875400 :=
  FiniteIntervals.of_fin 875200 200 complete_chunk4376

lemma complete_chunk4377 : ∀ i : Fin 200, Compatible (875400 + i.val) →
    (table.lookup (875400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4377 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 875400 875600 :=
  FiniteIntervals.of_fin 875400 200 complete_chunk4377

lemma complete_chunk4378 : ∀ i : Fin 200, Compatible (875600 + i.val) →
    (table.lookup (875600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4378 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 875600 875800 :=
  FiniteIntervals.of_fin 875600 200 complete_chunk4378

lemma complete_chunk4379 : ∀ i : Fin 200, Compatible (875800 + i.val) →
    (table.lookup (875800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4379 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 875800 876000 :=
  FiniteIntervals.of_fin 875800 200 complete_chunk4379

#print axioms interval_chunk4370
end Erdos184Work.PureFiveFilter4
