import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1380 : ∀ i : Fin 200, Compatible (276000 + i.val) →
    (table.lookup (276000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1380 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 276000 276200 :=
  FiniteIntervals.of_fin 276000 200 complete_chunk1380

lemma complete_chunk1381 : ∀ i : Fin 200, Compatible (276200 + i.val) →
    (table.lookup (276200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1381 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 276200 276400 :=
  FiniteIntervals.of_fin 276200 200 complete_chunk1381

lemma complete_chunk1382 : ∀ i : Fin 200, Compatible (276400 + i.val) →
    (table.lookup (276400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1382 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 276400 276600 :=
  FiniteIntervals.of_fin 276400 200 complete_chunk1382

lemma complete_chunk1383 : ∀ i : Fin 200, Compatible (276600 + i.val) →
    (table.lookup (276600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1383 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 276600 276800 :=
  FiniteIntervals.of_fin 276600 200 complete_chunk1383

lemma complete_chunk1384 : ∀ i : Fin 200, Compatible (276800 + i.val) →
    (table.lookup (276800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1384 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 276800 277000 :=
  FiniteIntervals.of_fin 276800 200 complete_chunk1384

lemma complete_chunk1385 : ∀ i : Fin 200, Compatible (277000 + i.val) →
    (table.lookup (277000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1385 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 277000 277200 :=
  FiniteIntervals.of_fin 277000 200 complete_chunk1385

lemma complete_chunk1386 : ∀ i : Fin 200, Compatible (277200 + i.val) →
    (table.lookup (277200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1386 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 277200 277400 :=
  FiniteIntervals.of_fin 277200 200 complete_chunk1386

lemma complete_chunk1387 : ∀ i : Fin 200, Compatible (277400 + i.val) →
    (table.lookup (277400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1387 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 277400 277600 :=
  FiniteIntervals.of_fin 277400 200 complete_chunk1387

lemma complete_chunk1388 : ∀ i : Fin 200, Compatible (277600 + i.val) →
    (table.lookup (277600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1388 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 277600 277800 :=
  FiniteIntervals.of_fin 277600 200 complete_chunk1388

lemma complete_chunk1389 : ∀ i : Fin 200, Compatible (277800 + i.val) →
    (table.lookup (277800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1389 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 277800 278000 :=
  FiniteIntervals.of_fin 277800 200 complete_chunk1389

#print axioms interval_chunk1380
end Erdos184Work.PureFiveFilter4
