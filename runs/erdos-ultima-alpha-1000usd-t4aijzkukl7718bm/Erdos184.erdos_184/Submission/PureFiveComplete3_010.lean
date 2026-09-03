import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk100 : ∀ i : Fin 200, Compatible (20000 + i.val) →
    (table.lookup (20000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk100 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 20000 20200 :=
  FiniteIntervals.of_fin 20000 200 complete_chunk100

lemma complete_chunk101 : ∀ i : Fin 200, Compatible (20200 + i.val) →
    (table.lookup (20200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk101 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 20200 20400 :=
  FiniteIntervals.of_fin 20200 200 complete_chunk101

lemma complete_chunk102 : ∀ i : Fin 200, Compatible (20400 + i.val) →
    (table.lookup (20400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk102 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 20400 20600 :=
  FiniteIntervals.of_fin 20400 200 complete_chunk102

lemma complete_chunk103 : ∀ i : Fin 200, Compatible (20600 + i.val) →
    (table.lookup (20600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk103 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 20600 20800 :=
  FiniteIntervals.of_fin 20600 200 complete_chunk103

lemma complete_chunk104 : ∀ i : Fin 200, Compatible (20800 + i.val) →
    (table.lookup (20800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk104 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 20800 21000 :=
  FiniteIntervals.of_fin 20800 200 complete_chunk104

lemma complete_chunk105 : ∀ i : Fin 200, Compatible (21000 + i.val) →
    (table.lookup (21000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk105 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 21000 21200 :=
  FiniteIntervals.of_fin 21000 200 complete_chunk105

lemma complete_chunk106 : ∀ i : Fin 200, Compatible (21200 + i.val) →
    (table.lookup (21200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk106 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 21200 21400 :=
  FiniteIntervals.of_fin 21200 200 complete_chunk106

lemma complete_chunk107 : ∀ i : Fin 200, Compatible (21400 + i.val) →
    (table.lookup (21400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk107 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 21400 21600 :=
  FiniteIntervals.of_fin 21400 200 complete_chunk107

lemma complete_chunk108 : ∀ i : Fin 200, Compatible (21600 + i.val) →
    (table.lookup (21600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk108 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 21600 21800 :=
  FiniteIntervals.of_fin 21600 200 complete_chunk108

lemma complete_chunk109 : ∀ i : Fin 200, Compatible (21800 + i.val) →
    (table.lookup (21800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk109 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 21800 22000 :=
  FiniteIntervals.of_fin 21800 200 complete_chunk109

#print axioms interval_chunk100
end Erdos184Work.PureFiveFilter3
