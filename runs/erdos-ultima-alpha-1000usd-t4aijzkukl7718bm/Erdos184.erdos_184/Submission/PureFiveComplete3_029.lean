import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk290 : ∀ i : Fin 200, Compatible (58000 + i.val) →
    (table.lookup (58000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk290 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58000 58200 :=
  FiniteIntervals.of_fin 58000 200 complete_chunk290

lemma complete_chunk291 : ∀ i : Fin 200, Compatible (58200 + i.val) →
    (table.lookup (58200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk291 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58200 58400 :=
  FiniteIntervals.of_fin 58200 200 complete_chunk291

lemma complete_chunk292 : ∀ i : Fin 200, Compatible (58400 + i.val) →
    (table.lookup (58400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk292 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58400 58600 :=
  FiniteIntervals.of_fin 58400 200 complete_chunk292

lemma complete_chunk293 : ∀ i : Fin 200, Compatible (58600 + i.val) →
    (table.lookup (58600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk293 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58600 58800 :=
  FiniteIntervals.of_fin 58600 200 complete_chunk293

lemma complete_chunk294 : ∀ i : Fin 200, Compatible (58800 + i.val) →
    (table.lookup (58800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk294 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58800 59000 :=
  FiniteIntervals.of_fin 58800 200 complete_chunk294

lemma complete_chunk295 : ∀ i : Fin 200, Compatible (59000 + i.val) →
    (table.lookup (59000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk295 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59000 59200 :=
  FiniteIntervals.of_fin 59000 200 complete_chunk295

lemma complete_chunk296 : ∀ i : Fin 200, Compatible (59200 + i.val) →
    (table.lookup (59200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk296 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59200 59400 :=
  FiniteIntervals.of_fin 59200 200 complete_chunk296

lemma complete_chunk297 : ∀ i : Fin 200, Compatible (59400 + i.val) →
    (table.lookup (59400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk297 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59400 59600 :=
  FiniteIntervals.of_fin 59400 200 complete_chunk297

lemma complete_chunk298 : ∀ i : Fin 200, Compatible (59600 + i.val) →
    (table.lookup (59600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk298 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59600 59800 :=
  FiniteIntervals.of_fin 59600 200 complete_chunk298

lemma complete_chunk299 : ∀ i : Fin 200, Compatible (59800 + i.val) →
    (table.lookup (59800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk299 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59800 60000 :=
  FiniteIntervals.of_fin 59800 200 complete_chunk299

#print axioms interval_chunk290
end Erdos184Work.PureFiveFilter3
