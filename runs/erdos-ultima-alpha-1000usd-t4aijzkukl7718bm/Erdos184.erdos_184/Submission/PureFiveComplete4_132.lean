import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1320 : ∀ i : Fin 200, Compatible (264000 + i.val) →
    (table.lookup (264000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1320 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 264000 264200 :=
  FiniteIntervals.of_fin 264000 200 complete_chunk1320

lemma complete_chunk1321 : ∀ i : Fin 200, Compatible (264200 + i.val) →
    (table.lookup (264200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1321 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 264200 264400 :=
  FiniteIntervals.of_fin 264200 200 complete_chunk1321

lemma complete_chunk1322 : ∀ i : Fin 200, Compatible (264400 + i.val) →
    (table.lookup (264400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1322 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 264400 264600 :=
  FiniteIntervals.of_fin 264400 200 complete_chunk1322

lemma complete_chunk1323 : ∀ i : Fin 200, Compatible (264600 + i.val) →
    (table.lookup (264600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1323 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 264600 264800 :=
  FiniteIntervals.of_fin 264600 200 complete_chunk1323

lemma complete_chunk1324 : ∀ i : Fin 200, Compatible (264800 + i.val) →
    (table.lookup (264800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1324 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 264800 265000 :=
  FiniteIntervals.of_fin 264800 200 complete_chunk1324

lemma complete_chunk1325 : ∀ i : Fin 200, Compatible (265000 + i.val) →
    (table.lookup (265000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1325 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 265000 265200 :=
  FiniteIntervals.of_fin 265000 200 complete_chunk1325

lemma complete_chunk1326 : ∀ i : Fin 200, Compatible (265200 + i.val) →
    (table.lookup (265200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1326 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 265200 265400 :=
  FiniteIntervals.of_fin 265200 200 complete_chunk1326

lemma complete_chunk1327 : ∀ i : Fin 200, Compatible (265400 + i.val) →
    (table.lookup (265400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1327 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 265400 265600 :=
  FiniteIntervals.of_fin 265400 200 complete_chunk1327

lemma complete_chunk1328 : ∀ i : Fin 200, Compatible (265600 + i.val) →
    (table.lookup (265600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1328 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 265600 265800 :=
  FiniteIntervals.of_fin 265600 200 complete_chunk1328

lemma complete_chunk1329 : ∀ i : Fin 200, Compatible (265800 + i.val) →
    (table.lookup (265800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1329 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 265800 266000 :=
  FiniteIntervals.of_fin 265800 200 complete_chunk1329

#print axioms interval_chunk1320
end Erdos184Work.PureFiveFilter4
