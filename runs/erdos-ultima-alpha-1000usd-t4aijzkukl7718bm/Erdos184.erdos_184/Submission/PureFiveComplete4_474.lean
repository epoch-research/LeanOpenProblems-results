import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4740 : ∀ i : Fin 200, Compatible (948000 + i.val) →
    (table.lookup (948000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4740 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 948000 948200 :=
  FiniteIntervals.of_fin 948000 200 complete_chunk4740

lemma complete_chunk4741 : ∀ i : Fin 200, Compatible (948200 + i.val) →
    (table.lookup (948200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4741 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 948200 948400 :=
  FiniteIntervals.of_fin 948200 200 complete_chunk4741

lemma complete_chunk4742 : ∀ i : Fin 200, Compatible (948400 + i.val) →
    (table.lookup (948400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4742 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 948400 948600 :=
  FiniteIntervals.of_fin 948400 200 complete_chunk4742

lemma complete_chunk4743 : ∀ i : Fin 200, Compatible (948600 + i.val) →
    (table.lookup (948600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4743 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 948600 948800 :=
  FiniteIntervals.of_fin 948600 200 complete_chunk4743

lemma complete_chunk4744 : ∀ i : Fin 200, Compatible (948800 + i.val) →
    (table.lookup (948800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4744 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 948800 949000 :=
  FiniteIntervals.of_fin 948800 200 complete_chunk4744

lemma complete_chunk4745 : ∀ i : Fin 200, Compatible (949000 + i.val) →
    (table.lookup (949000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4745 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 949000 949200 :=
  FiniteIntervals.of_fin 949000 200 complete_chunk4745

lemma complete_chunk4746 : ∀ i : Fin 200, Compatible (949200 + i.val) →
    (table.lookup (949200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4746 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 949200 949400 :=
  FiniteIntervals.of_fin 949200 200 complete_chunk4746

lemma complete_chunk4747 : ∀ i : Fin 200, Compatible (949400 + i.val) →
    (table.lookup (949400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4747 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 949400 949600 :=
  FiniteIntervals.of_fin 949400 200 complete_chunk4747

lemma complete_chunk4748 : ∀ i : Fin 200, Compatible (949600 + i.val) →
    (table.lookup (949600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4748 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 949600 949800 :=
  FiniteIntervals.of_fin 949600 200 complete_chunk4748

lemma complete_chunk4749 : ∀ i : Fin 200, Compatible (949800 + i.val) →
    (table.lookup (949800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4749 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 949800 950000 :=
  FiniteIntervals.of_fin 949800 200 complete_chunk4749

#print axioms interval_chunk4740
end Erdos184Work.PureFiveFilter4
