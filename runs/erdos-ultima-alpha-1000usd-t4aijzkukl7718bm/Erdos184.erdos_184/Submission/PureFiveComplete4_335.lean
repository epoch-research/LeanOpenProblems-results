import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3350 : ∀ i : Fin 200, Compatible (670000 + i.val) →
    (table.lookup (670000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3350 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 670000 670200 :=
  FiniteIntervals.of_fin 670000 200 complete_chunk3350

lemma complete_chunk3351 : ∀ i : Fin 200, Compatible (670200 + i.val) →
    (table.lookup (670200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3351 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 670200 670400 :=
  FiniteIntervals.of_fin 670200 200 complete_chunk3351

lemma complete_chunk3352 : ∀ i : Fin 200, Compatible (670400 + i.val) →
    (table.lookup (670400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3352 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 670400 670600 :=
  FiniteIntervals.of_fin 670400 200 complete_chunk3352

lemma complete_chunk3353 : ∀ i : Fin 200, Compatible (670600 + i.val) →
    (table.lookup (670600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3353 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 670600 670800 :=
  FiniteIntervals.of_fin 670600 200 complete_chunk3353

lemma complete_chunk3354 : ∀ i : Fin 200, Compatible (670800 + i.val) →
    (table.lookup (670800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3354 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 670800 671000 :=
  FiniteIntervals.of_fin 670800 200 complete_chunk3354

lemma complete_chunk3355 : ∀ i : Fin 200, Compatible (671000 + i.val) →
    (table.lookup (671000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3355 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 671000 671200 :=
  FiniteIntervals.of_fin 671000 200 complete_chunk3355

lemma complete_chunk3356 : ∀ i : Fin 200, Compatible (671200 + i.val) →
    (table.lookup (671200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3356 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 671200 671400 :=
  FiniteIntervals.of_fin 671200 200 complete_chunk3356

lemma complete_chunk3357 : ∀ i : Fin 200, Compatible (671400 + i.val) →
    (table.lookup (671400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3357 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 671400 671600 :=
  FiniteIntervals.of_fin 671400 200 complete_chunk3357

lemma complete_chunk3358 : ∀ i : Fin 200, Compatible (671600 + i.val) →
    (table.lookup (671600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3358 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 671600 671800 :=
  FiniteIntervals.of_fin 671600 200 complete_chunk3358

lemma complete_chunk3359 : ∀ i : Fin 200, Compatible (671800 + i.val) →
    (table.lookup (671800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3359 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 671800 672000 :=
  FiniteIntervals.of_fin 671800 200 complete_chunk3359

#print axioms interval_chunk3350
end Erdos184Work.PureFiveFilter4
