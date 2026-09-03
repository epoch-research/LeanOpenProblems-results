import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4580 : ∀ i : Fin 200, Compatible (916000 + i.val) →
    (table.lookup (916000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4580 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 916000 916200 :=
  FiniteIntervals.of_fin 916000 200 complete_chunk4580

lemma complete_chunk4581 : ∀ i : Fin 200, Compatible (916200 + i.val) →
    (table.lookup (916200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4581 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 916200 916400 :=
  FiniteIntervals.of_fin 916200 200 complete_chunk4581

lemma complete_chunk4582 : ∀ i : Fin 200, Compatible (916400 + i.val) →
    (table.lookup (916400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4582 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 916400 916600 :=
  FiniteIntervals.of_fin 916400 200 complete_chunk4582

lemma complete_chunk4583 : ∀ i : Fin 200, Compatible (916600 + i.val) →
    (table.lookup (916600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4583 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 916600 916800 :=
  FiniteIntervals.of_fin 916600 200 complete_chunk4583

lemma complete_chunk4584 : ∀ i : Fin 200, Compatible (916800 + i.val) →
    (table.lookup (916800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4584 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 916800 917000 :=
  FiniteIntervals.of_fin 916800 200 complete_chunk4584

lemma complete_chunk4585 : ∀ i : Fin 200, Compatible (917000 + i.val) →
    (table.lookup (917000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4585 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 917000 917200 :=
  FiniteIntervals.of_fin 917000 200 complete_chunk4585

lemma complete_chunk4586 : ∀ i : Fin 200, Compatible (917200 + i.val) →
    (table.lookup (917200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4586 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 917200 917400 :=
  FiniteIntervals.of_fin 917200 200 complete_chunk4586

lemma complete_chunk4587 : ∀ i : Fin 200, Compatible (917400 + i.val) →
    (table.lookup (917400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4587 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 917400 917600 :=
  FiniteIntervals.of_fin 917400 200 complete_chunk4587

lemma complete_chunk4588 : ∀ i : Fin 200, Compatible (917600 + i.val) →
    (table.lookup (917600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4588 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 917600 917800 :=
  FiniteIntervals.of_fin 917600 200 complete_chunk4588

lemma complete_chunk4589 : ∀ i : Fin 200, Compatible (917800 + i.val) →
    (table.lookup (917800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4589 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 917800 918000 :=
  FiniteIntervals.of_fin 917800 200 complete_chunk4589

#print axioms interval_chunk4580
end Erdos184Work.PureFiveFilter4
