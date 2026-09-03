import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5430 : ∀ i : Fin 200, Compatible (1086000 + i.val) →
    (table.lookup (1086000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5430 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1086000 1086200 :=
  FiniteIntervals.of_fin 1086000 200 complete_chunk5430

lemma complete_chunk5431 : ∀ i : Fin 200, Compatible (1086200 + i.val) →
    (table.lookup (1086200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5431 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1086200 1086400 :=
  FiniteIntervals.of_fin 1086200 200 complete_chunk5431

lemma complete_chunk5432 : ∀ i : Fin 200, Compatible (1086400 + i.val) →
    (table.lookup (1086400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5432 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1086400 1086600 :=
  FiniteIntervals.of_fin 1086400 200 complete_chunk5432

lemma complete_chunk5433 : ∀ i : Fin 200, Compatible (1086600 + i.val) →
    (table.lookup (1086600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5433 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1086600 1086800 :=
  FiniteIntervals.of_fin 1086600 200 complete_chunk5433

lemma complete_chunk5434 : ∀ i : Fin 200, Compatible (1086800 + i.val) →
    (table.lookup (1086800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5434 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1086800 1087000 :=
  FiniteIntervals.of_fin 1086800 200 complete_chunk5434

lemma complete_chunk5435 : ∀ i : Fin 200, Compatible (1087000 + i.val) →
    (table.lookup (1087000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5435 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1087000 1087200 :=
  FiniteIntervals.of_fin 1087000 200 complete_chunk5435

lemma complete_chunk5436 : ∀ i : Fin 200, Compatible (1087200 + i.val) →
    (table.lookup (1087200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5436 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1087200 1087400 :=
  FiniteIntervals.of_fin 1087200 200 complete_chunk5436

lemma complete_chunk5437 : ∀ i : Fin 200, Compatible (1087400 + i.val) →
    (table.lookup (1087400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5437 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1087400 1087600 :=
  FiniteIntervals.of_fin 1087400 200 complete_chunk5437

lemma complete_chunk5438 : ∀ i : Fin 200, Compatible (1087600 + i.val) →
    (table.lookup (1087600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5438 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1087600 1087800 :=
  FiniteIntervals.of_fin 1087600 200 complete_chunk5438

lemma complete_chunk5439 : ∀ i : Fin 200, Compatible (1087800 + i.val) →
    (table.lookup (1087800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5439 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1087800 1088000 :=
  FiniteIntervals.of_fin 1087800 200 complete_chunk5439

#print axioms interval_chunk5430
end Erdos184Work.PureFiveFilter4
