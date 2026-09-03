import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2570 : ∀ i : Fin 200, Compatible (514000 + i.val) →
    (table.lookup (514000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2570 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 514000 514200 :=
  FiniteIntervals.of_fin 514000 200 complete_chunk2570

lemma complete_chunk2571 : ∀ i : Fin 200, Compatible (514200 + i.val) →
    (table.lookup (514200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2571 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 514200 514400 :=
  FiniteIntervals.of_fin 514200 200 complete_chunk2571

lemma complete_chunk2572 : ∀ i : Fin 200, Compatible (514400 + i.val) →
    (table.lookup (514400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2572 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 514400 514600 :=
  FiniteIntervals.of_fin 514400 200 complete_chunk2572

lemma complete_chunk2573 : ∀ i : Fin 200, Compatible (514600 + i.val) →
    (table.lookup (514600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2573 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 514600 514800 :=
  FiniteIntervals.of_fin 514600 200 complete_chunk2573

lemma complete_chunk2574 : ∀ i : Fin 200, Compatible (514800 + i.val) →
    (table.lookup (514800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2574 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 514800 515000 :=
  FiniteIntervals.of_fin 514800 200 complete_chunk2574

lemma complete_chunk2575 : ∀ i : Fin 200, Compatible (515000 + i.val) →
    (table.lookup (515000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2575 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 515000 515200 :=
  FiniteIntervals.of_fin 515000 200 complete_chunk2575

lemma complete_chunk2576 : ∀ i : Fin 200, Compatible (515200 + i.val) →
    (table.lookup (515200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2576 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 515200 515400 :=
  FiniteIntervals.of_fin 515200 200 complete_chunk2576

lemma complete_chunk2577 : ∀ i : Fin 200, Compatible (515400 + i.val) →
    (table.lookup (515400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2577 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 515400 515600 :=
  FiniteIntervals.of_fin 515400 200 complete_chunk2577

lemma complete_chunk2578 : ∀ i : Fin 200, Compatible (515600 + i.val) →
    (table.lookup (515600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2578 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 515600 515800 :=
  FiniteIntervals.of_fin 515600 200 complete_chunk2578

lemma complete_chunk2579 : ∀ i : Fin 200, Compatible (515800 + i.val) →
    (table.lookup (515800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2579 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 515800 516000 :=
  FiniteIntervals.of_fin 515800 200 complete_chunk2579

#print axioms interval_chunk2570
end Erdos184Work.PureFiveFilter4
