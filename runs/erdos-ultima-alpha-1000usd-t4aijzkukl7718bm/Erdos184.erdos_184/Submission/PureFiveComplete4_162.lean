import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1620 : ∀ i : Fin 200, Compatible (324000 + i.val) →
    (table.lookup (324000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1620 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 324000 324200 :=
  FiniteIntervals.of_fin 324000 200 complete_chunk1620

lemma complete_chunk1621 : ∀ i : Fin 200, Compatible (324200 + i.val) →
    (table.lookup (324200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1621 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 324200 324400 :=
  FiniteIntervals.of_fin 324200 200 complete_chunk1621

lemma complete_chunk1622 : ∀ i : Fin 200, Compatible (324400 + i.val) →
    (table.lookup (324400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1622 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 324400 324600 :=
  FiniteIntervals.of_fin 324400 200 complete_chunk1622

lemma complete_chunk1623 : ∀ i : Fin 200, Compatible (324600 + i.val) →
    (table.lookup (324600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1623 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 324600 324800 :=
  FiniteIntervals.of_fin 324600 200 complete_chunk1623

lemma complete_chunk1624 : ∀ i : Fin 200, Compatible (324800 + i.val) →
    (table.lookup (324800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1624 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 324800 325000 :=
  FiniteIntervals.of_fin 324800 200 complete_chunk1624

lemma complete_chunk1625 : ∀ i : Fin 200, Compatible (325000 + i.val) →
    (table.lookup (325000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1625 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 325000 325200 :=
  FiniteIntervals.of_fin 325000 200 complete_chunk1625

lemma complete_chunk1626 : ∀ i : Fin 200, Compatible (325200 + i.val) →
    (table.lookup (325200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1626 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 325200 325400 :=
  FiniteIntervals.of_fin 325200 200 complete_chunk1626

lemma complete_chunk1627 : ∀ i : Fin 200, Compatible (325400 + i.val) →
    (table.lookup (325400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1627 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 325400 325600 :=
  FiniteIntervals.of_fin 325400 200 complete_chunk1627

lemma complete_chunk1628 : ∀ i : Fin 200, Compatible (325600 + i.val) →
    (table.lookup (325600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1628 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 325600 325800 :=
  FiniteIntervals.of_fin 325600 200 complete_chunk1628

lemma complete_chunk1629 : ∀ i : Fin 200, Compatible (325800 + i.val) →
    (table.lookup (325800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1629 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 325800 326000 :=
  FiniteIntervals.of_fin 325800 200 complete_chunk1629

#print axioms interval_chunk1620
end Erdos184Work.PureFiveFilter4
