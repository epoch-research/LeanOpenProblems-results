import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1610 : ∀ i : Fin 200, Compatible (322000 + i.val) →
    (table.lookup (322000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1610 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 322000 322200 :=
  FiniteIntervals.of_fin 322000 200 complete_chunk1610

lemma complete_chunk1611 : ∀ i : Fin 200, Compatible (322200 + i.val) →
    (table.lookup (322200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1611 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 322200 322400 :=
  FiniteIntervals.of_fin 322200 200 complete_chunk1611

lemma complete_chunk1612 : ∀ i : Fin 200, Compatible (322400 + i.val) →
    (table.lookup (322400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1612 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 322400 322600 :=
  FiniteIntervals.of_fin 322400 200 complete_chunk1612

lemma complete_chunk1613 : ∀ i : Fin 200, Compatible (322600 + i.val) →
    (table.lookup (322600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1613 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 322600 322800 :=
  FiniteIntervals.of_fin 322600 200 complete_chunk1613

lemma complete_chunk1614 : ∀ i : Fin 200, Compatible (322800 + i.val) →
    (table.lookup (322800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1614 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 322800 323000 :=
  FiniteIntervals.of_fin 322800 200 complete_chunk1614

lemma complete_chunk1615 : ∀ i : Fin 200, Compatible (323000 + i.val) →
    (table.lookup (323000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1615 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 323000 323200 :=
  FiniteIntervals.of_fin 323000 200 complete_chunk1615

lemma complete_chunk1616 : ∀ i : Fin 200, Compatible (323200 + i.val) →
    (table.lookup (323200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1616 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 323200 323400 :=
  FiniteIntervals.of_fin 323200 200 complete_chunk1616

lemma complete_chunk1617 : ∀ i : Fin 200, Compatible (323400 + i.val) →
    (table.lookup (323400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1617 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 323400 323600 :=
  FiniteIntervals.of_fin 323400 200 complete_chunk1617

lemma complete_chunk1618 : ∀ i : Fin 200, Compatible (323600 + i.val) →
    (table.lookup (323600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1618 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 323600 323800 :=
  FiniteIntervals.of_fin 323600 200 complete_chunk1618

lemma complete_chunk1619 : ∀ i : Fin 200, Compatible (323800 + i.val) →
    (table.lookup (323800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1619 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 323800 324000 :=
  FiniteIntervals.of_fin 323800 200 complete_chunk1619

#print axioms interval_chunk1610
end Erdos184Work.PureFiveFilter4
