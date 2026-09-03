import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5310 : ∀ i : Fin 200, Compatible (1062000 + i.val) →
    (table.lookup (1062000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5310 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1062000 1062200 :=
  FiniteIntervals.of_fin 1062000 200 complete_chunk5310

lemma complete_chunk5311 : ∀ i : Fin 200, Compatible (1062200 + i.val) →
    (table.lookup (1062200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5311 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1062200 1062400 :=
  FiniteIntervals.of_fin 1062200 200 complete_chunk5311

lemma complete_chunk5312 : ∀ i : Fin 200, Compatible (1062400 + i.val) →
    (table.lookup (1062400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5312 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1062400 1062600 :=
  FiniteIntervals.of_fin 1062400 200 complete_chunk5312

lemma complete_chunk5313 : ∀ i : Fin 200, Compatible (1062600 + i.val) →
    (table.lookup (1062600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5313 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1062600 1062800 :=
  FiniteIntervals.of_fin 1062600 200 complete_chunk5313

lemma complete_chunk5314 : ∀ i : Fin 200, Compatible (1062800 + i.val) →
    (table.lookup (1062800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5314 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1062800 1063000 :=
  FiniteIntervals.of_fin 1062800 200 complete_chunk5314

lemma complete_chunk5315 : ∀ i : Fin 200, Compatible (1063000 + i.val) →
    (table.lookup (1063000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5315 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1063000 1063200 :=
  FiniteIntervals.of_fin 1063000 200 complete_chunk5315

lemma complete_chunk5316 : ∀ i : Fin 200, Compatible (1063200 + i.val) →
    (table.lookup (1063200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5316 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1063200 1063400 :=
  FiniteIntervals.of_fin 1063200 200 complete_chunk5316

lemma complete_chunk5317 : ∀ i : Fin 200, Compatible (1063400 + i.val) →
    (table.lookup (1063400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5317 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1063400 1063600 :=
  FiniteIntervals.of_fin 1063400 200 complete_chunk5317

lemma complete_chunk5318 : ∀ i : Fin 200, Compatible (1063600 + i.val) →
    (table.lookup (1063600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5318 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1063600 1063800 :=
  FiniteIntervals.of_fin 1063600 200 complete_chunk5318

lemma complete_chunk5319 : ∀ i : Fin 200, Compatible (1063800 + i.val) →
    (table.lookup (1063800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5319 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1063800 1064000 :=
  FiniteIntervals.of_fin 1063800 200 complete_chunk5319

#print axioms interval_chunk5310
end Erdos184Work.PureFiveFilter4
