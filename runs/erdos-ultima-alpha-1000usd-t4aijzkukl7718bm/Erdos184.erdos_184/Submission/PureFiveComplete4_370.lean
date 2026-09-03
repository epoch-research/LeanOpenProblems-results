import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3700 : ∀ i : Fin 200, Compatible (740000 + i.val) →
    (table.lookup (740000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3700 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 740000 740200 :=
  FiniteIntervals.of_fin 740000 200 complete_chunk3700

lemma complete_chunk3701 : ∀ i : Fin 200, Compatible (740200 + i.val) →
    (table.lookup (740200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3701 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 740200 740400 :=
  FiniteIntervals.of_fin 740200 200 complete_chunk3701

lemma complete_chunk3702 : ∀ i : Fin 200, Compatible (740400 + i.val) →
    (table.lookup (740400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3702 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 740400 740600 :=
  FiniteIntervals.of_fin 740400 200 complete_chunk3702

lemma complete_chunk3703 : ∀ i : Fin 200, Compatible (740600 + i.val) →
    (table.lookup (740600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3703 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 740600 740800 :=
  FiniteIntervals.of_fin 740600 200 complete_chunk3703

lemma complete_chunk3704 : ∀ i : Fin 200, Compatible (740800 + i.val) →
    (table.lookup (740800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3704 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 740800 741000 :=
  FiniteIntervals.of_fin 740800 200 complete_chunk3704

lemma complete_chunk3705 : ∀ i : Fin 200, Compatible (741000 + i.val) →
    (table.lookup (741000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3705 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 741000 741200 :=
  FiniteIntervals.of_fin 741000 200 complete_chunk3705

lemma complete_chunk3706 : ∀ i : Fin 200, Compatible (741200 + i.val) →
    (table.lookup (741200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3706 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 741200 741400 :=
  FiniteIntervals.of_fin 741200 200 complete_chunk3706

lemma complete_chunk3707 : ∀ i : Fin 200, Compatible (741400 + i.val) →
    (table.lookup (741400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3707 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 741400 741600 :=
  FiniteIntervals.of_fin 741400 200 complete_chunk3707

lemma complete_chunk3708 : ∀ i : Fin 200, Compatible (741600 + i.val) →
    (table.lookup (741600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3708 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 741600 741800 :=
  FiniteIntervals.of_fin 741600 200 complete_chunk3708

lemma complete_chunk3709 : ∀ i : Fin 200, Compatible (741800 + i.val) →
    (table.lookup (741800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3709 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 741800 742000 :=
  FiniteIntervals.of_fin 741800 200 complete_chunk3709

#print axioms interval_chunk3700
end Erdos184Work.PureFiveFilter4
