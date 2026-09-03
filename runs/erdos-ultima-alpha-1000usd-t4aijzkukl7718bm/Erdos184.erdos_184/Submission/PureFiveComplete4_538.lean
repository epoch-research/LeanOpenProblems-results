import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5380 : ∀ i : Fin 200, Compatible (1076000 + i.val) →
    (table.lookup (1076000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5380 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1076000 1076200 :=
  FiniteIntervals.of_fin 1076000 200 complete_chunk5380

lemma complete_chunk5381 : ∀ i : Fin 200, Compatible (1076200 + i.val) →
    (table.lookup (1076200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5381 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1076200 1076400 :=
  FiniteIntervals.of_fin 1076200 200 complete_chunk5381

lemma complete_chunk5382 : ∀ i : Fin 200, Compatible (1076400 + i.val) →
    (table.lookup (1076400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5382 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1076400 1076600 :=
  FiniteIntervals.of_fin 1076400 200 complete_chunk5382

lemma complete_chunk5383 : ∀ i : Fin 200, Compatible (1076600 + i.val) →
    (table.lookup (1076600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5383 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1076600 1076800 :=
  FiniteIntervals.of_fin 1076600 200 complete_chunk5383

lemma complete_chunk5384 : ∀ i : Fin 200, Compatible (1076800 + i.val) →
    (table.lookup (1076800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5384 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1076800 1077000 :=
  FiniteIntervals.of_fin 1076800 200 complete_chunk5384

lemma complete_chunk5385 : ∀ i : Fin 200, Compatible (1077000 + i.val) →
    (table.lookup (1077000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5385 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1077000 1077200 :=
  FiniteIntervals.of_fin 1077000 200 complete_chunk5385

lemma complete_chunk5386 : ∀ i : Fin 200, Compatible (1077200 + i.val) →
    (table.lookup (1077200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5386 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1077200 1077400 :=
  FiniteIntervals.of_fin 1077200 200 complete_chunk5386

lemma complete_chunk5387 : ∀ i : Fin 200, Compatible (1077400 + i.val) →
    (table.lookup (1077400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5387 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1077400 1077600 :=
  FiniteIntervals.of_fin 1077400 200 complete_chunk5387

lemma complete_chunk5388 : ∀ i : Fin 200, Compatible (1077600 + i.val) →
    (table.lookup (1077600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5388 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1077600 1077800 :=
  FiniteIntervals.of_fin 1077600 200 complete_chunk5388

lemma complete_chunk5389 : ∀ i : Fin 200, Compatible (1077800 + i.val) →
    (table.lookup (1077800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5389 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1077800 1078000 :=
  FiniteIntervals.of_fin 1077800 200 complete_chunk5389

#print axioms interval_chunk5380
end Erdos184Work.PureFiveFilter4
