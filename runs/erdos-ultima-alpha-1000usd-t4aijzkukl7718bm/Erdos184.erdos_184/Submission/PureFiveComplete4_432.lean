import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4320 : ∀ i : Fin 200, Compatible (864000 + i.val) →
    (table.lookup (864000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4320 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 864000 864200 :=
  FiniteIntervals.of_fin 864000 200 complete_chunk4320

lemma complete_chunk4321 : ∀ i : Fin 200, Compatible (864200 + i.val) →
    (table.lookup (864200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4321 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 864200 864400 :=
  FiniteIntervals.of_fin 864200 200 complete_chunk4321

lemma complete_chunk4322 : ∀ i : Fin 200, Compatible (864400 + i.val) →
    (table.lookup (864400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4322 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 864400 864600 :=
  FiniteIntervals.of_fin 864400 200 complete_chunk4322

lemma complete_chunk4323 : ∀ i : Fin 200, Compatible (864600 + i.val) →
    (table.lookup (864600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4323 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 864600 864800 :=
  FiniteIntervals.of_fin 864600 200 complete_chunk4323

lemma complete_chunk4324 : ∀ i : Fin 200, Compatible (864800 + i.val) →
    (table.lookup (864800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4324 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 864800 865000 :=
  FiniteIntervals.of_fin 864800 200 complete_chunk4324

lemma complete_chunk4325 : ∀ i : Fin 200, Compatible (865000 + i.val) →
    (table.lookup (865000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4325 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 865000 865200 :=
  FiniteIntervals.of_fin 865000 200 complete_chunk4325

lemma complete_chunk4326 : ∀ i : Fin 200, Compatible (865200 + i.val) →
    (table.lookup (865200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4326 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 865200 865400 :=
  FiniteIntervals.of_fin 865200 200 complete_chunk4326

lemma complete_chunk4327 : ∀ i : Fin 200, Compatible (865400 + i.val) →
    (table.lookup (865400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4327 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 865400 865600 :=
  FiniteIntervals.of_fin 865400 200 complete_chunk4327

lemma complete_chunk4328 : ∀ i : Fin 200, Compatible (865600 + i.val) →
    (table.lookup (865600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4328 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 865600 865800 :=
  FiniteIntervals.of_fin 865600 200 complete_chunk4328

lemma complete_chunk4329 : ∀ i : Fin 200, Compatible (865800 + i.val) →
    (table.lookup (865800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4329 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 865800 866000 :=
  FiniteIntervals.of_fin 865800 200 complete_chunk4329

#print axioms interval_chunk4320
end Erdos184Work.PureFiveFilter4
