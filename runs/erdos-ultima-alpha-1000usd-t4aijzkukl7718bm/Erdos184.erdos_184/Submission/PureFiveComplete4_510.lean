import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5100 : ∀ i : Fin 200, Compatible (1020000 + i.val) →
    (table.lookup (1020000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5100 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1020000 1020200 :=
  FiniteIntervals.of_fin 1020000 200 complete_chunk5100

lemma complete_chunk5101 : ∀ i : Fin 200, Compatible (1020200 + i.val) →
    (table.lookup (1020200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5101 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1020200 1020400 :=
  FiniteIntervals.of_fin 1020200 200 complete_chunk5101

lemma complete_chunk5102 : ∀ i : Fin 200, Compatible (1020400 + i.val) →
    (table.lookup (1020400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5102 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1020400 1020600 :=
  FiniteIntervals.of_fin 1020400 200 complete_chunk5102

lemma complete_chunk5103 : ∀ i : Fin 200, Compatible (1020600 + i.val) →
    (table.lookup (1020600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5103 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1020600 1020800 :=
  FiniteIntervals.of_fin 1020600 200 complete_chunk5103

lemma complete_chunk5104 : ∀ i : Fin 200, Compatible (1020800 + i.val) →
    (table.lookup (1020800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5104 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1020800 1021000 :=
  FiniteIntervals.of_fin 1020800 200 complete_chunk5104

lemma complete_chunk5105 : ∀ i : Fin 200, Compatible (1021000 + i.val) →
    (table.lookup (1021000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5105 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1021000 1021200 :=
  FiniteIntervals.of_fin 1021000 200 complete_chunk5105

lemma complete_chunk5106 : ∀ i : Fin 200, Compatible (1021200 + i.val) →
    (table.lookup (1021200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5106 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1021200 1021400 :=
  FiniteIntervals.of_fin 1021200 200 complete_chunk5106

lemma complete_chunk5107 : ∀ i : Fin 200, Compatible (1021400 + i.val) →
    (table.lookup (1021400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5107 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1021400 1021600 :=
  FiniteIntervals.of_fin 1021400 200 complete_chunk5107

lemma complete_chunk5108 : ∀ i : Fin 200, Compatible (1021600 + i.val) →
    (table.lookup (1021600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5108 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1021600 1021800 :=
  FiniteIntervals.of_fin 1021600 200 complete_chunk5108

lemma complete_chunk5109 : ∀ i : Fin 200, Compatible (1021800 + i.val) →
    (table.lookup (1021800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5109 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1021800 1022000 :=
  FiniteIntervals.of_fin 1021800 200 complete_chunk5109

#print axioms interval_chunk5100
end Erdos184Work.PureFiveFilter4
