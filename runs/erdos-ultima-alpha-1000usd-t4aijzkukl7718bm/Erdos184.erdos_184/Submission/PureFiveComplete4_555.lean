import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5550 : ∀ i : Fin 200, Compatible (1110000 + i.val) →
    (table.lookup (1110000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5550 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1110000 1110200 :=
  FiniteIntervals.of_fin 1110000 200 complete_chunk5550

lemma complete_chunk5551 : ∀ i : Fin 200, Compatible (1110200 + i.val) →
    (table.lookup (1110200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5551 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1110200 1110400 :=
  FiniteIntervals.of_fin 1110200 200 complete_chunk5551

lemma complete_chunk5552 : ∀ i : Fin 200, Compatible (1110400 + i.val) →
    (table.lookup (1110400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5552 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1110400 1110600 :=
  FiniteIntervals.of_fin 1110400 200 complete_chunk5552

lemma complete_chunk5553 : ∀ i : Fin 200, Compatible (1110600 + i.val) →
    (table.lookup (1110600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5553 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1110600 1110800 :=
  FiniteIntervals.of_fin 1110600 200 complete_chunk5553

lemma complete_chunk5554 : ∀ i : Fin 200, Compatible (1110800 + i.val) →
    (table.lookup (1110800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5554 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1110800 1111000 :=
  FiniteIntervals.of_fin 1110800 200 complete_chunk5554

lemma complete_chunk5555 : ∀ i : Fin 200, Compatible (1111000 + i.val) →
    (table.lookup (1111000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5555 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1111000 1111200 :=
  FiniteIntervals.of_fin 1111000 200 complete_chunk5555

lemma complete_chunk5556 : ∀ i : Fin 200, Compatible (1111200 + i.val) →
    (table.lookup (1111200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5556 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1111200 1111400 :=
  FiniteIntervals.of_fin 1111200 200 complete_chunk5556

lemma complete_chunk5557 : ∀ i : Fin 200, Compatible (1111400 + i.val) →
    (table.lookup (1111400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5557 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1111400 1111600 :=
  FiniteIntervals.of_fin 1111400 200 complete_chunk5557

lemma complete_chunk5558 : ∀ i : Fin 200, Compatible (1111600 + i.val) →
    (table.lookup (1111600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5558 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1111600 1111800 :=
  FiniteIntervals.of_fin 1111600 200 complete_chunk5558

lemma complete_chunk5559 : ∀ i : Fin 200, Compatible (1111800 + i.val) →
    (table.lookup (1111800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5559 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1111800 1112000 :=
  FiniteIntervals.of_fin 1111800 200 complete_chunk5559

#print axioms interval_chunk5550
end Erdos184Work.PureFiveFilter4
