import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1790 : ∀ i : Fin 200, Compatible (358000 + i.val) →
    (table.lookup (358000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1790 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 358000 358200 :=
  FiniteIntervals.of_fin 358000 200 complete_chunk1790

lemma complete_chunk1791 : ∀ i : Fin 200, Compatible (358200 + i.val) →
    (table.lookup (358200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1791 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 358200 358400 :=
  FiniteIntervals.of_fin 358200 200 complete_chunk1791

lemma complete_chunk1792 : ∀ i : Fin 200, Compatible (358400 + i.val) →
    (table.lookup (358400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1792 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 358400 358600 :=
  FiniteIntervals.of_fin 358400 200 complete_chunk1792

lemma complete_chunk1793 : ∀ i : Fin 200, Compatible (358600 + i.val) →
    (table.lookup (358600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1793 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 358600 358800 :=
  FiniteIntervals.of_fin 358600 200 complete_chunk1793

lemma complete_chunk1794 : ∀ i : Fin 200, Compatible (358800 + i.val) →
    (table.lookup (358800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1794 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 358800 359000 :=
  FiniteIntervals.of_fin 358800 200 complete_chunk1794

lemma complete_chunk1795 : ∀ i : Fin 200, Compatible (359000 + i.val) →
    (table.lookup (359000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1795 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 359000 359200 :=
  FiniteIntervals.of_fin 359000 200 complete_chunk1795

lemma complete_chunk1796 : ∀ i : Fin 200, Compatible (359200 + i.val) →
    (table.lookup (359200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1796 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 359200 359400 :=
  FiniteIntervals.of_fin 359200 200 complete_chunk1796

lemma complete_chunk1797 : ∀ i : Fin 200, Compatible (359400 + i.val) →
    (table.lookup (359400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1797 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 359400 359600 :=
  FiniteIntervals.of_fin 359400 200 complete_chunk1797

lemma complete_chunk1798 : ∀ i : Fin 200, Compatible (359600 + i.val) →
    (table.lookup (359600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1798 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 359600 359800 :=
  FiniteIntervals.of_fin 359600 200 complete_chunk1798

lemma complete_chunk1799 : ∀ i : Fin 200, Compatible (359800 + i.val) →
    (table.lookup (359800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1799 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 359800 360000 :=
  FiniteIntervals.of_fin 359800 200 complete_chunk1799

#print axioms interval_chunk1790
end Erdos184Work.PureFiveFilter4
