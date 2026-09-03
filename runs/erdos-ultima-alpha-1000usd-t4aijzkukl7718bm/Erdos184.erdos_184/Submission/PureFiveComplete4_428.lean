import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4280 : ∀ i : Fin 200, Compatible (856000 + i.val) →
    (table.lookup (856000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4280 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 856000 856200 :=
  FiniteIntervals.of_fin 856000 200 complete_chunk4280

lemma complete_chunk4281 : ∀ i : Fin 200, Compatible (856200 + i.val) →
    (table.lookup (856200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4281 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 856200 856400 :=
  FiniteIntervals.of_fin 856200 200 complete_chunk4281

lemma complete_chunk4282 : ∀ i : Fin 200, Compatible (856400 + i.val) →
    (table.lookup (856400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4282 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 856400 856600 :=
  FiniteIntervals.of_fin 856400 200 complete_chunk4282

lemma complete_chunk4283 : ∀ i : Fin 200, Compatible (856600 + i.val) →
    (table.lookup (856600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4283 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 856600 856800 :=
  FiniteIntervals.of_fin 856600 200 complete_chunk4283

lemma complete_chunk4284 : ∀ i : Fin 200, Compatible (856800 + i.val) →
    (table.lookup (856800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4284 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 856800 857000 :=
  FiniteIntervals.of_fin 856800 200 complete_chunk4284

lemma complete_chunk4285 : ∀ i : Fin 200, Compatible (857000 + i.val) →
    (table.lookup (857000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4285 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 857000 857200 :=
  FiniteIntervals.of_fin 857000 200 complete_chunk4285

lemma complete_chunk4286 : ∀ i : Fin 200, Compatible (857200 + i.val) →
    (table.lookup (857200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4286 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 857200 857400 :=
  FiniteIntervals.of_fin 857200 200 complete_chunk4286

lemma complete_chunk4287 : ∀ i : Fin 200, Compatible (857400 + i.val) →
    (table.lookup (857400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4287 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 857400 857600 :=
  FiniteIntervals.of_fin 857400 200 complete_chunk4287

lemma complete_chunk4288 : ∀ i : Fin 200, Compatible (857600 + i.val) →
    (table.lookup (857600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4288 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 857600 857800 :=
  FiniteIntervals.of_fin 857600 200 complete_chunk4288

lemma complete_chunk4289 : ∀ i : Fin 200, Compatible (857800 + i.val) →
    (table.lookup (857800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4289 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 857800 858000 :=
  FiniteIntervals.of_fin 857800 200 complete_chunk4289

#print axioms interval_chunk4280
end Erdos184Work.PureFiveFilter4
