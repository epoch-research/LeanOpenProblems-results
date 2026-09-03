import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5360 : ∀ i : Fin 200, Compatible (1072000 + i.val) →
    (table.lookup (1072000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5360 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1072000 1072200 :=
  FiniteIntervals.of_fin 1072000 200 complete_chunk5360

lemma complete_chunk5361 : ∀ i : Fin 200, Compatible (1072200 + i.val) →
    (table.lookup (1072200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5361 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1072200 1072400 :=
  FiniteIntervals.of_fin 1072200 200 complete_chunk5361

lemma complete_chunk5362 : ∀ i : Fin 200, Compatible (1072400 + i.val) →
    (table.lookup (1072400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5362 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1072400 1072600 :=
  FiniteIntervals.of_fin 1072400 200 complete_chunk5362

lemma complete_chunk5363 : ∀ i : Fin 200, Compatible (1072600 + i.val) →
    (table.lookup (1072600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5363 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1072600 1072800 :=
  FiniteIntervals.of_fin 1072600 200 complete_chunk5363

lemma complete_chunk5364 : ∀ i : Fin 200, Compatible (1072800 + i.val) →
    (table.lookup (1072800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5364 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1072800 1073000 :=
  FiniteIntervals.of_fin 1072800 200 complete_chunk5364

lemma complete_chunk5365 : ∀ i : Fin 200, Compatible (1073000 + i.val) →
    (table.lookup (1073000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5365 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1073000 1073200 :=
  FiniteIntervals.of_fin 1073000 200 complete_chunk5365

lemma complete_chunk5366 : ∀ i : Fin 200, Compatible (1073200 + i.val) →
    (table.lookup (1073200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5366 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1073200 1073400 :=
  FiniteIntervals.of_fin 1073200 200 complete_chunk5366

lemma complete_chunk5367 : ∀ i : Fin 200, Compatible (1073400 + i.val) →
    (table.lookup (1073400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5367 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1073400 1073600 :=
  FiniteIntervals.of_fin 1073400 200 complete_chunk5367

lemma complete_chunk5368 : ∀ i : Fin 200, Compatible (1073600 + i.val) →
    (table.lookup (1073600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5368 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1073600 1073800 :=
  FiniteIntervals.of_fin 1073600 200 complete_chunk5368

lemma complete_chunk5369 : ∀ i : Fin 200, Compatible (1073800 + i.val) →
    (table.lookup (1073800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5369 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1073800 1074000 :=
  FiniteIntervals.of_fin 1073800 200 complete_chunk5369

#print axioms interval_chunk5360
end Erdos184Work.PureFiveFilter4
