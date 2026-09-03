import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk600 : ∀ i : Fin 200, Compatible (120000 + i.val) →
    (table.lookup (120000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk600 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 120000 120200 :=
  FiniteIntervals.of_fin 120000 200 complete_chunk600

lemma complete_chunk601 : ∀ i : Fin 200, Compatible (120200 + i.val) →
    (table.lookup (120200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk601 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 120200 120400 :=
  FiniteIntervals.of_fin 120200 200 complete_chunk601

lemma complete_chunk602 : ∀ i : Fin 200, Compatible (120400 + i.val) →
    (table.lookup (120400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk602 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 120400 120600 :=
  FiniteIntervals.of_fin 120400 200 complete_chunk602

lemma complete_chunk603 : ∀ i : Fin 200, Compatible (120600 + i.val) →
    (table.lookup (120600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk603 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 120600 120800 :=
  FiniteIntervals.of_fin 120600 200 complete_chunk603

lemma complete_chunk604 : ∀ i : Fin 200, Compatible (120800 + i.val) →
    (table.lookup (120800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk604 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 120800 121000 :=
  FiniteIntervals.of_fin 120800 200 complete_chunk604

lemma complete_chunk605 : ∀ i : Fin 200, Compatible (121000 + i.val) →
    (table.lookup (121000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk605 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 121000 121200 :=
  FiniteIntervals.of_fin 121000 200 complete_chunk605

lemma complete_chunk606 : ∀ i : Fin 200, Compatible (121200 + i.val) →
    (table.lookup (121200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk606 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 121200 121400 :=
  FiniteIntervals.of_fin 121200 200 complete_chunk606

lemma complete_chunk607 : ∀ i : Fin 200, Compatible (121400 + i.val) →
    (table.lookup (121400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk607 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 121400 121600 :=
  FiniteIntervals.of_fin 121400 200 complete_chunk607

lemma complete_chunk608 : ∀ i : Fin 200, Compatible (121600 + i.val) →
    (table.lookup (121600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk608 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 121600 121800 :=
  FiniteIntervals.of_fin 121600 200 complete_chunk608

lemma complete_chunk609 : ∀ i : Fin 200, Compatible (121800 + i.val) →
    (table.lookup (121800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk609 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 121800 122000 :=
  FiniteIntervals.of_fin 121800 200 complete_chunk609

#print axioms interval_chunk600
end Erdos184Work.PureFiveFilter4
