import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1680 : ∀ i : Fin 200, Compatible (336000 + i.val) →
    (table.lookup (336000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1680 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 336000 336200 :=
  FiniteIntervals.of_fin 336000 200 complete_chunk1680

lemma complete_chunk1681 : ∀ i : Fin 200, Compatible (336200 + i.val) →
    (table.lookup (336200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1681 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 336200 336400 :=
  FiniteIntervals.of_fin 336200 200 complete_chunk1681

lemma complete_chunk1682 : ∀ i : Fin 200, Compatible (336400 + i.val) →
    (table.lookup (336400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1682 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 336400 336600 :=
  FiniteIntervals.of_fin 336400 200 complete_chunk1682

lemma complete_chunk1683 : ∀ i : Fin 200, Compatible (336600 + i.val) →
    (table.lookup (336600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1683 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 336600 336800 :=
  FiniteIntervals.of_fin 336600 200 complete_chunk1683

lemma complete_chunk1684 : ∀ i : Fin 200, Compatible (336800 + i.val) →
    (table.lookup (336800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1684 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 336800 337000 :=
  FiniteIntervals.of_fin 336800 200 complete_chunk1684

lemma complete_chunk1685 : ∀ i : Fin 200, Compatible (337000 + i.val) →
    (table.lookup (337000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1685 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 337000 337200 :=
  FiniteIntervals.of_fin 337000 200 complete_chunk1685

lemma complete_chunk1686 : ∀ i : Fin 200, Compatible (337200 + i.val) →
    (table.lookup (337200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1686 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 337200 337400 :=
  FiniteIntervals.of_fin 337200 200 complete_chunk1686

lemma complete_chunk1687 : ∀ i : Fin 200, Compatible (337400 + i.val) →
    (table.lookup (337400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1687 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 337400 337600 :=
  FiniteIntervals.of_fin 337400 200 complete_chunk1687

lemma complete_chunk1688 : ∀ i : Fin 200, Compatible (337600 + i.val) →
    (table.lookup (337600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1688 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 337600 337800 :=
  FiniteIntervals.of_fin 337600 200 complete_chunk1688

lemma complete_chunk1689 : ∀ i : Fin 200, Compatible (337800 + i.val) →
    (table.lookup (337800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1689 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 337800 338000 :=
  FiniteIntervals.of_fin 337800 200 complete_chunk1689

#print axioms interval_chunk1680
end Erdos184Work.PureFiveFilter4
