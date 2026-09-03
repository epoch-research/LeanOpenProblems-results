import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3360 : ∀ i : Fin 200, Compatible (672000 + i.val) →
    (table.lookup (672000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3360 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 672000 672200 :=
  FiniteIntervals.of_fin 672000 200 complete_chunk3360

lemma complete_chunk3361 : ∀ i : Fin 200, Compatible (672200 + i.val) →
    (table.lookup (672200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3361 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 672200 672400 :=
  FiniteIntervals.of_fin 672200 200 complete_chunk3361

lemma complete_chunk3362 : ∀ i : Fin 200, Compatible (672400 + i.val) →
    (table.lookup (672400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3362 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 672400 672600 :=
  FiniteIntervals.of_fin 672400 200 complete_chunk3362

lemma complete_chunk3363 : ∀ i : Fin 200, Compatible (672600 + i.val) →
    (table.lookup (672600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3363 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 672600 672800 :=
  FiniteIntervals.of_fin 672600 200 complete_chunk3363

lemma complete_chunk3364 : ∀ i : Fin 200, Compatible (672800 + i.val) →
    (table.lookup (672800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3364 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 672800 673000 :=
  FiniteIntervals.of_fin 672800 200 complete_chunk3364

lemma complete_chunk3365 : ∀ i : Fin 200, Compatible (673000 + i.val) →
    (table.lookup (673000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3365 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 673000 673200 :=
  FiniteIntervals.of_fin 673000 200 complete_chunk3365

lemma complete_chunk3366 : ∀ i : Fin 200, Compatible (673200 + i.val) →
    (table.lookup (673200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3366 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 673200 673400 :=
  FiniteIntervals.of_fin 673200 200 complete_chunk3366

lemma complete_chunk3367 : ∀ i : Fin 200, Compatible (673400 + i.val) →
    (table.lookup (673400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3367 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 673400 673600 :=
  FiniteIntervals.of_fin 673400 200 complete_chunk3367

lemma complete_chunk3368 : ∀ i : Fin 200, Compatible (673600 + i.val) →
    (table.lookup (673600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3368 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 673600 673800 :=
  FiniteIntervals.of_fin 673600 200 complete_chunk3368

lemma complete_chunk3369 : ∀ i : Fin 200, Compatible (673800 + i.val) →
    (table.lookup (673800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3369 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 673800 674000 :=
  FiniteIntervals.of_fin 673800 200 complete_chunk3369

#print axioms interval_chunk3360
end Erdos184Work.PureFiveFilter4
