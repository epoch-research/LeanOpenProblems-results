import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5570 : ∀ i : Fin 200, Compatible (1114000 + i.val) →
    (table.lookup (1114000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5570 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1114000 1114200 :=
  FiniteIntervals.of_fin 1114000 200 complete_chunk5570

lemma complete_chunk5571 : ∀ i : Fin 200, Compatible (1114200 + i.val) →
    (table.lookup (1114200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5571 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1114200 1114400 :=
  FiniteIntervals.of_fin 1114200 200 complete_chunk5571

lemma complete_chunk5572 : ∀ i : Fin 200, Compatible (1114400 + i.val) →
    (table.lookup (1114400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5572 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1114400 1114600 :=
  FiniteIntervals.of_fin 1114400 200 complete_chunk5572

lemma complete_chunk5573 : ∀ i : Fin 200, Compatible (1114600 + i.val) →
    (table.lookup (1114600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5573 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1114600 1114800 :=
  FiniteIntervals.of_fin 1114600 200 complete_chunk5573

lemma complete_chunk5574 : ∀ i : Fin 200, Compatible (1114800 + i.val) →
    (table.lookup (1114800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5574 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1114800 1115000 :=
  FiniteIntervals.of_fin 1114800 200 complete_chunk5574

lemma complete_chunk5575 : ∀ i : Fin 200, Compatible (1115000 + i.val) →
    (table.lookup (1115000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5575 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1115000 1115200 :=
  FiniteIntervals.of_fin 1115000 200 complete_chunk5575

lemma complete_chunk5576 : ∀ i : Fin 200, Compatible (1115200 + i.val) →
    (table.lookup (1115200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5576 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1115200 1115400 :=
  FiniteIntervals.of_fin 1115200 200 complete_chunk5576

lemma complete_chunk5577 : ∀ i : Fin 200, Compatible (1115400 + i.val) →
    (table.lookup (1115400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5577 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1115400 1115600 :=
  FiniteIntervals.of_fin 1115400 200 complete_chunk5577

lemma complete_chunk5578 : ∀ i : Fin 200, Compatible (1115600 + i.val) →
    (table.lookup (1115600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5578 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1115600 1115800 :=
  FiniteIntervals.of_fin 1115600 200 complete_chunk5578

lemma complete_chunk5579 : ∀ i : Fin 200, Compatible (1115800 + i.val) →
    (table.lookup (1115800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5579 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1115800 1116000 :=
  FiniteIntervals.of_fin 1115800 200 complete_chunk5579

#print axioms interval_chunk5570
end Erdos184Work.PureFiveFilter4
