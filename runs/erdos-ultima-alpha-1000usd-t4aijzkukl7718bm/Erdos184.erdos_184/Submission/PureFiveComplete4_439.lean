import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4390 : ∀ i : Fin 200, Compatible (878000 + i.val) →
    (table.lookup (878000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4390 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 878000 878200 :=
  FiniteIntervals.of_fin 878000 200 complete_chunk4390

lemma complete_chunk4391 : ∀ i : Fin 200, Compatible (878200 + i.val) →
    (table.lookup (878200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4391 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 878200 878400 :=
  FiniteIntervals.of_fin 878200 200 complete_chunk4391

lemma complete_chunk4392 : ∀ i : Fin 200, Compatible (878400 + i.val) →
    (table.lookup (878400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4392 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 878400 878600 :=
  FiniteIntervals.of_fin 878400 200 complete_chunk4392

lemma complete_chunk4393 : ∀ i : Fin 200, Compatible (878600 + i.val) →
    (table.lookup (878600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4393 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 878600 878800 :=
  FiniteIntervals.of_fin 878600 200 complete_chunk4393

lemma complete_chunk4394 : ∀ i : Fin 200, Compatible (878800 + i.val) →
    (table.lookup (878800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4394 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 878800 879000 :=
  FiniteIntervals.of_fin 878800 200 complete_chunk4394

lemma complete_chunk4395 : ∀ i : Fin 200, Compatible (879000 + i.val) →
    (table.lookup (879000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4395 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 879000 879200 :=
  FiniteIntervals.of_fin 879000 200 complete_chunk4395

lemma complete_chunk4396 : ∀ i : Fin 200, Compatible (879200 + i.val) →
    (table.lookup (879200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4396 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 879200 879400 :=
  FiniteIntervals.of_fin 879200 200 complete_chunk4396

lemma complete_chunk4397 : ∀ i : Fin 200, Compatible (879400 + i.val) →
    (table.lookup (879400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4397 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 879400 879600 :=
  FiniteIntervals.of_fin 879400 200 complete_chunk4397

lemma complete_chunk4398 : ∀ i : Fin 200, Compatible (879600 + i.val) →
    (table.lookup (879600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4398 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 879600 879800 :=
  FiniteIntervals.of_fin 879600 200 complete_chunk4398

lemma complete_chunk4399 : ∀ i : Fin 200, Compatible (879800 + i.val) →
    (table.lookup (879800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4399 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 879800 880000 :=
  FiniteIntervals.of_fin 879800 200 complete_chunk4399

#print axioms interval_chunk4390
end Erdos184Work.PureFiveFilter4
