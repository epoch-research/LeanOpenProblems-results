import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1580 : ∀ i : Fin 200, Compatible (316000 + i.val) →
    (table.lookup (316000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1580 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 316000 316200 :=
  FiniteIntervals.of_fin 316000 200 complete_chunk1580

lemma complete_chunk1581 : ∀ i : Fin 200, Compatible (316200 + i.val) →
    (table.lookup (316200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1581 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 316200 316400 :=
  FiniteIntervals.of_fin 316200 200 complete_chunk1581

lemma complete_chunk1582 : ∀ i : Fin 200, Compatible (316400 + i.val) →
    (table.lookup (316400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1582 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 316400 316600 :=
  FiniteIntervals.of_fin 316400 200 complete_chunk1582

lemma complete_chunk1583 : ∀ i : Fin 200, Compatible (316600 + i.val) →
    (table.lookup (316600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1583 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 316600 316800 :=
  FiniteIntervals.of_fin 316600 200 complete_chunk1583

lemma complete_chunk1584 : ∀ i : Fin 200, Compatible (316800 + i.val) →
    (table.lookup (316800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1584 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 316800 317000 :=
  FiniteIntervals.of_fin 316800 200 complete_chunk1584

lemma complete_chunk1585 : ∀ i : Fin 200, Compatible (317000 + i.val) →
    (table.lookup (317000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1585 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 317000 317200 :=
  FiniteIntervals.of_fin 317000 200 complete_chunk1585

lemma complete_chunk1586 : ∀ i : Fin 200, Compatible (317200 + i.val) →
    (table.lookup (317200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1586 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 317200 317400 :=
  FiniteIntervals.of_fin 317200 200 complete_chunk1586

lemma complete_chunk1587 : ∀ i : Fin 200, Compatible (317400 + i.val) →
    (table.lookup (317400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1587 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 317400 317600 :=
  FiniteIntervals.of_fin 317400 200 complete_chunk1587

lemma complete_chunk1588 : ∀ i : Fin 200, Compatible (317600 + i.val) →
    (table.lookup (317600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1588 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 317600 317800 :=
  FiniteIntervals.of_fin 317600 200 complete_chunk1588

lemma complete_chunk1589 : ∀ i : Fin 200, Compatible (317800 + i.val) →
    (table.lookup (317800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1589 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 317800 318000 :=
  FiniteIntervals.of_fin 317800 200 complete_chunk1589

#print axioms interval_chunk1580
end Erdos184Work.PureFiveFilter4
