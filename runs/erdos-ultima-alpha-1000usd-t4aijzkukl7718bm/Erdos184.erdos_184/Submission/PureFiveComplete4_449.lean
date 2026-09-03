import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4490 : ∀ i : Fin 200, Compatible (898000 + i.val) →
    (table.lookup (898000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4490 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 898000 898200 :=
  FiniteIntervals.of_fin 898000 200 complete_chunk4490

lemma complete_chunk4491 : ∀ i : Fin 200, Compatible (898200 + i.val) →
    (table.lookup (898200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4491 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 898200 898400 :=
  FiniteIntervals.of_fin 898200 200 complete_chunk4491

lemma complete_chunk4492 : ∀ i : Fin 200, Compatible (898400 + i.val) →
    (table.lookup (898400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4492 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 898400 898600 :=
  FiniteIntervals.of_fin 898400 200 complete_chunk4492

lemma complete_chunk4493 : ∀ i : Fin 200, Compatible (898600 + i.val) →
    (table.lookup (898600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4493 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 898600 898800 :=
  FiniteIntervals.of_fin 898600 200 complete_chunk4493

lemma complete_chunk4494 : ∀ i : Fin 200, Compatible (898800 + i.val) →
    (table.lookup (898800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4494 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 898800 899000 :=
  FiniteIntervals.of_fin 898800 200 complete_chunk4494

lemma complete_chunk4495 : ∀ i : Fin 200, Compatible (899000 + i.val) →
    (table.lookup (899000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4495 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 899000 899200 :=
  FiniteIntervals.of_fin 899000 200 complete_chunk4495

lemma complete_chunk4496 : ∀ i : Fin 200, Compatible (899200 + i.val) →
    (table.lookup (899200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4496 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 899200 899400 :=
  FiniteIntervals.of_fin 899200 200 complete_chunk4496

lemma complete_chunk4497 : ∀ i : Fin 200, Compatible (899400 + i.val) →
    (table.lookup (899400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4497 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 899400 899600 :=
  FiniteIntervals.of_fin 899400 200 complete_chunk4497

lemma complete_chunk4498 : ∀ i : Fin 200, Compatible (899600 + i.val) →
    (table.lookup (899600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4498 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 899600 899800 :=
  FiniteIntervals.of_fin 899600 200 complete_chunk4498

lemma complete_chunk4499 : ∀ i : Fin 200, Compatible (899800 + i.val) →
    (table.lookup (899800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4499 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 899800 900000 :=
  FiniteIntervals.of_fin 899800 200 complete_chunk4499

#print axioms interval_chunk4490
end Erdos184Work.PureFiveFilter4
