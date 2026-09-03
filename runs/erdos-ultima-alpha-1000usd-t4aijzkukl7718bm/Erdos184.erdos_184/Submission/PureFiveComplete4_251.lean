import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2510 : ∀ i : Fin 200, Compatible (502000 + i.val) →
    (table.lookup (502000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2510 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 502000 502200 :=
  FiniteIntervals.of_fin 502000 200 complete_chunk2510

lemma complete_chunk2511 : ∀ i : Fin 200, Compatible (502200 + i.val) →
    (table.lookup (502200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2511 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 502200 502400 :=
  FiniteIntervals.of_fin 502200 200 complete_chunk2511

lemma complete_chunk2512 : ∀ i : Fin 200, Compatible (502400 + i.val) →
    (table.lookup (502400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2512 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 502400 502600 :=
  FiniteIntervals.of_fin 502400 200 complete_chunk2512

lemma complete_chunk2513 : ∀ i : Fin 200, Compatible (502600 + i.val) →
    (table.lookup (502600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2513 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 502600 502800 :=
  FiniteIntervals.of_fin 502600 200 complete_chunk2513

lemma complete_chunk2514 : ∀ i : Fin 200, Compatible (502800 + i.val) →
    (table.lookup (502800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2514 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 502800 503000 :=
  FiniteIntervals.of_fin 502800 200 complete_chunk2514

lemma complete_chunk2515 : ∀ i : Fin 200, Compatible (503000 + i.val) →
    (table.lookup (503000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2515 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 503000 503200 :=
  FiniteIntervals.of_fin 503000 200 complete_chunk2515

lemma complete_chunk2516 : ∀ i : Fin 200, Compatible (503200 + i.val) →
    (table.lookup (503200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2516 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 503200 503400 :=
  FiniteIntervals.of_fin 503200 200 complete_chunk2516

lemma complete_chunk2517 : ∀ i : Fin 200, Compatible (503400 + i.val) →
    (table.lookup (503400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2517 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 503400 503600 :=
  FiniteIntervals.of_fin 503400 200 complete_chunk2517

lemma complete_chunk2518 : ∀ i : Fin 200, Compatible (503600 + i.val) →
    (table.lookup (503600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2518 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 503600 503800 :=
  FiniteIntervals.of_fin 503600 200 complete_chunk2518

lemma complete_chunk2519 : ∀ i : Fin 200, Compatible (503800 + i.val) →
    (table.lookup (503800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2519 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 503800 504000 :=
  FiniteIntervals.of_fin 503800 200 complete_chunk2519

#print axioms interval_chunk2510
end Erdos184Work.PureFiveFilter4
