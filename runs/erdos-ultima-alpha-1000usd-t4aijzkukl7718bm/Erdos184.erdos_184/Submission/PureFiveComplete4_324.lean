import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3240 : ∀ i : Fin 200, Compatible (648000 + i.val) →
    (table.lookup (648000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3240 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 648000 648200 :=
  FiniteIntervals.of_fin 648000 200 complete_chunk3240

lemma complete_chunk3241 : ∀ i : Fin 200, Compatible (648200 + i.val) →
    (table.lookup (648200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3241 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 648200 648400 :=
  FiniteIntervals.of_fin 648200 200 complete_chunk3241

lemma complete_chunk3242 : ∀ i : Fin 200, Compatible (648400 + i.val) →
    (table.lookup (648400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3242 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 648400 648600 :=
  FiniteIntervals.of_fin 648400 200 complete_chunk3242

lemma complete_chunk3243 : ∀ i : Fin 200, Compatible (648600 + i.val) →
    (table.lookup (648600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3243 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 648600 648800 :=
  FiniteIntervals.of_fin 648600 200 complete_chunk3243

lemma complete_chunk3244 : ∀ i : Fin 200, Compatible (648800 + i.val) →
    (table.lookup (648800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3244 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 648800 649000 :=
  FiniteIntervals.of_fin 648800 200 complete_chunk3244

lemma complete_chunk3245 : ∀ i : Fin 200, Compatible (649000 + i.val) →
    (table.lookup (649000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3245 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 649000 649200 :=
  FiniteIntervals.of_fin 649000 200 complete_chunk3245

lemma complete_chunk3246 : ∀ i : Fin 200, Compatible (649200 + i.val) →
    (table.lookup (649200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3246 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 649200 649400 :=
  FiniteIntervals.of_fin 649200 200 complete_chunk3246

lemma complete_chunk3247 : ∀ i : Fin 200, Compatible (649400 + i.val) →
    (table.lookup (649400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3247 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 649400 649600 :=
  FiniteIntervals.of_fin 649400 200 complete_chunk3247

lemma complete_chunk3248 : ∀ i : Fin 200, Compatible (649600 + i.val) →
    (table.lookup (649600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3248 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 649600 649800 :=
  FiniteIntervals.of_fin 649600 200 complete_chunk3248

lemma complete_chunk3249 : ∀ i : Fin 200, Compatible (649800 + i.val) →
    (table.lookup (649800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3249 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 649800 650000 :=
  FiniteIntervals.of_fin 649800 200 complete_chunk3249

#print axioms interval_chunk3240
end Erdos184Work.PureFiveFilter4
