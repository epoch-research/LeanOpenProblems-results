import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk280 : ∀ i : Fin 200, Compatible (56000 + i.val) →
    (table.lookup (56000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk280 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56000 56200 :=
  FiniteIntervals.of_fin 56000 200 complete_chunk280

lemma complete_chunk281 : ∀ i : Fin 200, Compatible (56200 + i.val) →
    (table.lookup (56200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk281 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56200 56400 :=
  FiniteIntervals.of_fin 56200 200 complete_chunk281

lemma complete_chunk282 : ∀ i : Fin 200, Compatible (56400 + i.val) →
    (table.lookup (56400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk282 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56400 56600 :=
  FiniteIntervals.of_fin 56400 200 complete_chunk282

lemma complete_chunk283 : ∀ i : Fin 200, Compatible (56600 + i.val) →
    (table.lookup (56600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk283 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56600 56800 :=
  FiniteIntervals.of_fin 56600 200 complete_chunk283

lemma complete_chunk284 : ∀ i : Fin 200, Compatible (56800 + i.val) →
    (table.lookup (56800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk284 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56800 57000 :=
  FiniteIntervals.of_fin 56800 200 complete_chunk284

lemma complete_chunk285 : ∀ i : Fin 200, Compatible (57000 + i.val) →
    (table.lookup (57000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk285 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57000 57200 :=
  FiniteIntervals.of_fin 57000 200 complete_chunk285

lemma complete_chunk286 : ∀ i : Fin 200, Compatible (57200 + i.val) →
    (table.lookup (57200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk286 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57200 57400 :=
  FiniteIntervals.of_fin 57200 200 complete_chunk286

lemma complete_chunk287 : ∀ i : Fin 200, Compatible (57400 + i.val) →
    (table.lookup (57400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk287 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57400 57600 :=
  FiniteIntervals.of_fin 57400 200 complete_chunk287

lemma complete_chunk288 : ∀ i : Fin 200, Compatible (57600 + i.val) →
    (table.lookup (57600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk288 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57600 57800 :=
  FiniteIntervals.of_fin 57600 200 complete_chunk288

lemma complete_chunk289 : ∀ i : Fin 200, Compatible (57800 + i.val) →
    (table.lookup (57800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk289 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57800 58000 :=
  FiniteIntervals.of_fin 57800 200 complete_chunk289

#print axioms interval_chunk280
end Erdos184Work.PureFiveFilter3
