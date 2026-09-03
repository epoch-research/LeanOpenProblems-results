import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1690 : ∀ i : Fin 200, Compatible (338000 + i.val) →
    (table.lookup (338000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1690 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 338000 338200 :=
  FiniteIntervals.of_fin 338000 200 complete_chunk1690

lemma complete_chunk1691 : ∀ i : Fin 200, Compatible (338200 + i.val) →
    (table.lookup (338200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1691 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 338200 338400 :=
  FiniteIntervals.of_fin 338200 200 complete_chunk1691

lemma complete_chunk1692 : ∀ i : Fin 200, Compatible (338400 + i.val) →
    (table.lookup (338400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1692 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 338400 338600 :=
  FiniteIntervals.of_fin 338400 200 complete_chunk1692

lemma complete_chunk1693 : ∀ i : Fin 200, Compatible (338600 + i.val) →
    (table.lookup (338600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1693 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 338600 338800 :=
  FiniteIntervals.of_fin 338600 200 complete_chunk1693

lemma complete_chunk1694 : ∀ i : Fin 200, Compatible (338800 + i.val) →
    (table.lookup (338800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1694 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 338800 339000 :=
  FiniteIntervals.of_fin 338800 200 complete_chunk1694

lemma complete_chunk1695 : ∀ i : Fin 200, Compatible (339000 + i.val) →
    (table.lookup (339000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1695 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 339000 339200 :=
  FiniteIntervals.of_fin 339000 200 complete_chunk1695

lemma complete_chunk1696 : ∀ i : Fin 200, Compatible (339200 + i.val) →
    (table.lookup (339200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1696 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 339200 339400 :=
  FiniteIntervals.of_fin 339200 200 complete_chunk1696

lemma complete_chunk1697 : ∀ i : Fin 200, Compatible (339400 + i.val) →
    (table.lookup (339400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1697 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 339400 339600 :=
  FiniteIntervals.of_fin 339400 200 complete_chunk1697

lemma complete_chunk1698 : ∀ i : Fin 200, Compatible (339600 + i.val) →
    (table.lookup (339600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1698 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 339600 339800 :=
  FiniteIntervals.of_fin 339600 200 complete_chunk1698

lemma complete_chunk1699 : ∀ i : Fin 200, Compatible (339800 + i.val) →
    (table.lookup (339800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1699 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 339800 340000 :=
  FiniteIntervals.of_fin 339800 200 complete_chunk1699

#print axioms interval_chunk1690
end Erdos184Work.PureFiveFilter4
