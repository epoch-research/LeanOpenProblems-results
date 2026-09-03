import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4430 : ∀ i : Fin 200, Compatible (886000 + i.val) →
    (table.lookup (886000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4430 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 886000 886200 :=
  FiniteIntervals.of_fin 886000 200 complete_chunk4430

lemma complete_chunk4431 : ∀ i : Fin 200, Compatible (886200 + i.val) →
    (table.lookup (886200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4431 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 886200 886400 :=
  FiniteIntervals.of_fin 886200 200 complete_chunk4431

lemma complete_chunk4432 : ∀ i : Fin 200, Compatible (886400 + i.val) →
    (table.lookup (886400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4432 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 886400 886600 :=
  FiniteIntervals.of_fin 886400 200 complete_chunk4432

lemma complete_chunk4433 : ∀ i : Fin 200, Compatible (886600 + i.val) →
    (table.lookup (886600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4433 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 886600 886800 :=
  FiniteIntervals.of_fin 886600 200 complete_chunk4433

lemma complete_chunk4434 : ∀ i : Fin 200, Compatible (886800 + i.val) →
    (table.lookup (886800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4434 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 886800 887000 :=
  FiniteIntervals.of_fin 886800 200 complete_chunk4434

lemma complete_chunk4435 : ∀ i : Fin 200, Compatible (887000 + i.val) →
    (table.lookup (887000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4435 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 887000 887200 :=
  FiniteIntervals.of_fin 887000 200 complete_chunk4435

lemma complete_chunk4436 : ∀ i : Fin 200, Compatible (887200 + i.val) →
    (table.lookup (887200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4436 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 887200 887400 :=
  FiniteIntervals.of_fin 887200 200 complete_chunk4436

lemma complete_chunk4437 : ∀ i : Fin 200, Compatible (887400 + i.val) →
    (table.lookup (887400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4437 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 887400 887600 :=
  FiniteIntervals.of_fin 887400 200 complete_chunk4437

lemma complete_chunk4438 : ∀ i : Fin 200, Compatible (887600 + i.val) →
    (table.lookup (887600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4438 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 887600 887800 :=
  FiniteIntervals.of_fin 887600 200 complete_chunk4438

lemma complete_chunk4439 : ∀ i : Fin 200, Compatible (887800 + i.val) →
    (table.lookup (887800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4439 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 887800 888000 :=
  FiniteIntervals.of_fin 887800 200 complete_chunk4439

#print axioms interval_chunk4430
end Erdos184Work.PureFiveFilter4
