import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2610 : ∀ i : Fin 200, Compatible (522000 + i.val) →
    (table.lookup (522000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2610 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 522000 522200 :=
  FiniteIntervals.of_fin 522000 200 complete_chunk2610

lemma complete_chunk2611 : ∀ i : Fin 200, Compatible (522200 + i.val) →
    (table.lookup (522200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2611 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 522200 522400 :=
  FiniteIntervals.of_fin 522200 200 complete_chunk2611

lemma complete_chunk2612 : ∀ i : Fin 200, Compatible (522400 + i.val) →
    (table.lookup (522400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2612 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 522400 522600 :=
  FiniteIntervals.of_fin 522400 200 complete_chunk2612

lemma complete_chunk2613 : ∀ i : Fin 200, Compatible (522600 + i.val) →
    (table.lookup (522600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2613 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 522600 522800 :=
  FiniteIntervals.of_fin 522600 200 complete_chunk2613

lemma complete_chunk2614 : ∀ i : Fin 200, Compatible (522800 + i.val) →
    (table.lookup (522800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2614 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 522800 523000 :=
  FiniteIntervals.of_fin 522800 200 complete_chunk2614

lemma complete_chunk2615 : ∀ i : Fin 200, Compatible (523000 + i.val) →
    (table.lookup (523000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2615 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 523000 523200 :=
  FiniteIntervals.of_fin 523000 200 complete_chunk2615

lemma complete_chunk2616 : ∀ i : Fin 200, Compatible (523200 + i.val) →
    (table.lookup (523200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2616 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 523200 523400 :=
  FiniteIntervals.of_fin 523200 200 complete_chunk2616

lemma complete_chunk2617 : ∀ i : Fin 200, Compatible (523400 + i.val) →
    (table.lookup (523400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2617 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 523400 523600 :=
  FiniteIntervals.of_fin 523400 200 complete_chunk2617

lemma complete_chunk2618 : ∀ i : Fin 200, Compatible (523600 + i.val) →
    (table.lookup (523600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2618 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 523600 523800 :=
  FiniteIntervals.of_fin 523600 200 complete_chunk2618

lemma complete_chunk2619 : ∀ i : Fin 200, Compatible (523800 + i.val) →
    (table.lookup (523800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2619 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 523800 524000 :=
  FiniteIntervals.of_fin 523800 200 complete_chunk2619

#print axioms interval_chunk2610
end Erdos184Work.PureFiveFilter4
