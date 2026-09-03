import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2420 : ∀ i : Fin 200, Compatible (484000 + i.val) →
    (table.lookup (484000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2420 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 484000 484200 :=
  FiniteIntervals.of_fin 484000 200 complete_chunk2420

lemma complete_chunk2421 : ∀ i : Fin 200, Compatible (484200 + i.val) →
    (table.lookup (484200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2421 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 484200 484400 :=
  FiniteIntervals.of_fin 484200 200 complete_chunk2421

lemma complete_chunk2422 : ∀ i : Fin 200, Compatible (484400 + i.val) →
    (table.lookup (484400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2422 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 484400 484600 :=
  FiniteIntervals.of_fin 484400 200 complete_chunk2422

lemma complete_chunk2423 : ∀ i : Fin 200, Compatible (484600 + i.val) →
    (table.lookup (484600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2423 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 484600 484800 :=
  FiniteIntervals.of_fin 484600 200 complete_chunk2423

lemma complete_chunk2424 : ∀ i : Fin 200, Compatible (484800 + i.val) →
    (table.lookup (484800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2424 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 484800 485000 :=
  FiniteIntervals.of_fin 484800 200 complete_chunk2424

lemma complete_chunk2425 : ∀ i : Fin 200, Compatible (485000 + i.val) →
    (table.lookup (485000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2425 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 485000 485200 :=
  FiniteIntervals.of_fin 485000 200 complete_chunk2425

lemma complete_chunk2426 : ∀ i : Fin 200, Compatible (485200 + i.val) →
    (table.lookup (485200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2426 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 485200 485400 :=
  FiniteIntervals.of_fin 485200 200 complete_chunk2426

lemma complete_chunk2427 : ∀ i : Fin 200, Compatible (485400 + i.val) →
    (table.lookup (485400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2427 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 485400 485600 :=
  FiniteIntervals.of_fin 485400 200 complete_chunk2427

lemma complete_chunk2428 : ∀ i : Fin 200, Compatible (485600 + i.val) →
    (table.lookup (485600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2428 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 485600 485800 :=
  FiniteIntervals.of_fin 485600 200 complete_chunk2428

lemma complete_chunk2429 : ∀ i : Fin 200, Compatible (485800 + i.val) →
    (table.lookup (485800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2429 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 485800 486000 :=
  FiniteIntervals.of_fin 485800 200 complete_chunk2429

#print axioms interval_chunk2420
end Erdos184Work.PureFiveFilter4
