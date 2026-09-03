import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1590 : ∀ i : Fin 200, Compatible (318000 + i.val) →
    (table.lookup (318000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1590 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 318000 318200 :=
  FiniteIntervals.of_fin 318000 200 complete_chunk1590

lemma complete_chunk1591 : ∀ i : Fin 200, Compatible (318200 + i.val) →
    (table.lookup (318200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1591 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 318200 318400 :=
  FiniteIntervals.of_fin 318200 200 complete_chunk1591

lemma complete_chunk1592 : ∀ i : Fin 200, Compatible (318400 + i.val) →
    (table.lookup (318400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1592 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 318400 318600 :=
  FiniteIntervals.of_fin 318400 200 complete_chunk1592

lemma complete_chunk1593 : ∀ i : Fin 200, Compatible (318600 + i.val) →
    (table.lookup (318600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1593 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 318600 318800 :=
  FiniteIntervals.of_fin 318600 200 complete_chunk1593

lemma complete_chunk1594 : ∀ i : Fin 200, Compatible (318800 + i.val) →
    (table.lookup (318800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1594 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 318800 319000 :=
  FiniteIntervals.of_fin 318800 200 complete_chunk1594

lemma complete_chunk1595 : ∀ i : Fin 200, Compatible (319000 + i.val) →
    (table.lookup (319000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1595 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 319000 319200 :=
  FiniteIntervals.of_fin 319000 200 complete_chunk1595

lemma complete_chunk1596 : ∀ i : Fin 200, Compatible (319200 + i.val) →
    (table.lookup (319200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1596 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 319200 319400 :=
  FiniteIntervals.of_fin 319200 200 complete_chunk1596

lemma complete_chunk1597 : ∀ i : Fin 200, Compatible (319400 + i.val) →
    (table.lookup (319400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1597 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 319400 319600 :=
  FiniteIntervals.of_fin 319400 200 complete_chunk1597

lemma complete_chunk1598 : ∀ i : Fin 200, Compatible (319600 + i.val) →
    (table.lookup (319600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1598 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 319600 319800 :=
  FiniteIntervals.of_fin 319600 200 complete_chunk1598

lemma complete_chunk1599 : ∀ i : Fin 200, Compatible (319800 + i.val) →
    (table.lookup (319800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1599 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 319800 320000 :=
  FiniteIntervals.of_fin 319800 200 complete_chunk1599

#print axioms interval_chunk1590
end Erdos184Work.PureFiveFilter4
