import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4420 : ∀ i : Fin 200, Compatible (884000 + i.val) →
    (table.lookup (884000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4420 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 884000 884200 :=
  FiniteIntervals.of_fin 884000 200 complete_chunk4420

lemma complete_chunk4421 : ∀ i : Fin 200, Compatible (884200 + i.val) →
    (table.lookup (884200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4421 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 884200 884400 :=
  FiniteIntervals.of_fin 884200 200 complete_chunk4421

lemma complete_chunk4422 : ∀ i : Fin 200, Compatible (884400 + i.val) →
    (table.lookup (884400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4422 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 884400 884600 :=
  FiniteIntervals.of_fin 884400 200 complete_chunk4422

lemma complete_chunk4423 : ∀ i : Fin 200, Compatible (884600 + i.val) →
    (table.lookup (884600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4423 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 884600 884800 :=
  FiniteIntervals.of_fin 884600 200 complete_chunk4423

lemma complete_chunk4424 : ∀ i : Fin 200, Compatible (884800 + i.val) →
    (table.lookup (884800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4424 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 884800 885000 :=
  FiniteIntervals.of_fin 884800 200 complete_chunk4424

lemma complete_chunk4425 : ∀ i : Fin 200, Compatible (885000 + i.val) →
    (table.lookup (885000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4425 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 885000 885200 :=
  FiniteIntervals.of_fin 885000 200 complete_chunk4425

lemma complete_chunk4426 : ∀ i : Fin 200, Compatible (885200 + i.val) →
    (table.lookup (885200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4426 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 885200 885400 :=
  FiniteIntervals.of_fin 885200 200 complete_chunk4426

lemma complete_chunk4427 : ∀ i : Fin 200, Compatible (885400 + i.val) →
    (table.lookup (885400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4427 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 885400 885600 :=
  FiniteIntervals.of_fin 885400 200 complete_chunk4427

lemma complete_chunk4428 : ∀ i : Fin 200, Compatible (885600 + i.val) →
    (table.lookup (885600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4428 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 885600 885800 :=
  FiniteIntervals.of_fin 885600 200 complete_chunk4428

lemma complete_chunk4429 : ∀ i : Fin 200, Compatible (885800 + i.val) →
    (table.lookup (885800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4429 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 885800 886000 :=
  FiniteIntervals.of_fin 885800 200 complete_chunk4429

#print axioms interval_chunk4420
end Erdos184Work.PureFiveFilter4
