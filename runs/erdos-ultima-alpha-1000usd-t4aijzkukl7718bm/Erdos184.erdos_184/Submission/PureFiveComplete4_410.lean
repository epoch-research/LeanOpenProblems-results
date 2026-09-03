import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4100 : ∀ i : Fin 200, Compatible (820000 + i.val) →
    (table.lookup (820000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4100 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 820000 820200 :=
  FiniteIntervals.of_fin 820000 200 complete_chunk4100

lemma complete_chunk4101 : ∀ i : Fin 200, Compatible (820200 + i.val) →
    (table.lookup (820200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4101 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 820200 820400 :=
  FiniteIntervals.of_fin 820200 200 complete_chunk4101

lemma complete_chunk4102 : ∀ i : Fin 200, Compatible (820400 + i.val) →
    (table.lookup (820400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4102 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 820400 820600 :=
  FiniteIntervals.of_fin 820400 200 complete_chunk4102

lemma complete_chunk4103 : ∀ i : Fin 200, Compatible (820600 + i.val) →
    (table.lookup (820600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4103 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 820600 820800 :=
  FiniteIntervals.of_fin 820600 200 complete_chunk4103

lemma complete_chunk4104 : ∀ i : Fin 200, Compatible (820800 + i.val) →
    (table.lookup (820800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4104 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 820800 821000 :=
  FiniteIntervals.of_fin 820800 200 complete_chunk4104

lemma complete_chunk4105 : ∀ i : Fin 200, Compatible (821000 + i.val) →
    (table.lookup (821000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4105 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 821000 821200 :=
  FiniteIntervals.of_fin 821000 200 complete_chunk4105

lemma complete_chunk4106 : ∀ i : Fin 200, Compatible (821200 + i.val) →
    (table.lookup (821200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4106 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 821200 821400 :=
  FiniteIntervals.of_fin 821200 200 complete_chunk4106

lemma complete_chunk4107 : ∀ i : Fin 200, Compatible (821400 + i.val) →
    (table.lookup (821400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4107 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 821400 821600 :=
  FiniteIntervals.of_fin 821400 200 complete_chunk4107

lemma complete_chunk4108 : ∀ i : Fin 200, Compatible (821600 + i.val) →
    (table.lookup (821600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4108 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 821600 821800 :=
  FiniteIntervals.of_fin 821600 200 complete_chunk4108

lemma complete_chunk4109 : ∀ i : Fin 200, Compatible (821800 + i.val) →
    (table.lookup (821800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4109 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 821800 822000 :=
  FiniteIntervals.of_fin 821800 200 complete_chunk4109

#print axioms interval_chunk4100
end Erdos184Work.PureFiveFilter4
