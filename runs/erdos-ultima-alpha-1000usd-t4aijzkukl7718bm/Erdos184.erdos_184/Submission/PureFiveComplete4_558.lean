import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5580 : ∀ i : Fin 200, Compatible (1116000 + i.val) →
    (table.lookup (1116000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5580 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1116000 1116200 :=
  FiniteIntervals.of_fin 1116000 200 complete_chunk5580

lemma complete_chunk5581 : ∀ i : Fin 200, Compatible (1116200 + i.val) →
    (table.lookup (1116200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5581 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1116200 1116400 :=
  FiniteIntervals.of_fin 1116200 200 complete_chunk5581

lemma complete_chunk5582 : ∀ i : Fin 200, Compatible (1116400 + i.val) →
    (table.lookup (1116400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5582 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1116400 1116600 :=
  FiniteIntervals.of_fin 1116400 200 complete_chunk5582

lemma complete_chunk5583 : ∀ i : Fin 200, Compatible (1116600 + i.val) →
    (table.lookup (1116600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5583 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1116600 1116800 :=
  FiniteIntervals.of_fin 1116600 200 complete_chunk5583

lemma complete_chunk5584 : ∀ i : Fin 200, Compatible (1116800 + i.val) →
    (table.lookup (1116800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5584 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1116800 1117000 :=
  FiniteIntervals.of_fin 1116800 200 complete_chunk5584

lemma complete_chunk5585 : ∀ i : Fin 200, Compatible (1117000 + i.val) →
    (table.lookup (1117000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5585 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1117000 1117200 :=
  FiniteIntervals.of_fin 1117000 200 complete_chunk5585

lemma complete_chunk5586 : ∀ i : Fin 200, Compatible (1117200 + i.val) →
    (table.lookup (1117200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5586 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1117200 1117400 :=
  FiniteIntervals.of_fin 1117200 200 complete_chunk5586

lemma complete_chunk5587 : ∀ i : Fin 200, Compatible (1117400 + i.val) →
    (table.lookup (1117400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5587 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1117400 1117600 :=
  FiniteIntervals.of_fin 1117400 200 complete_chunk5587

lemma complete_chunk5588 : ∀ i : Fin 200, Compatible (1117600 + i.val) →
    (table.lookup (1117600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5588 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1117600 1117800 :=
  FiniteIntervals.of_fin 1117600 200 complete_chunk5588

lemma complete_chunk5589 : ∀ i : Fin 200, Compatible (1117800 + i.val) →
    (table.lookup (1117800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5589 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1117800 1118000 :=
  FiniteIntervals.of_fin 1117800 200 complete_chunk5589

#print axioms interval_chunk5580
end Erdos184Work.PureFiveFilter4
