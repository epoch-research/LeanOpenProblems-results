import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1710 : ∀ i : Fin 200, Compatible (342000 + i.val) →
    (table.lookup (342000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1710 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 342000 342200 :=
  FiniteIntervals.of_fin 342000 200 complete_chunk1710

lemma complete_chunk1711 : ∀ i : Fin 200, Compatible (342200 + i.val) →
    (table.lookup (342200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1711 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 342200 342400 :=
  FiniteIntervals.of_fin 342200 200 complete_chunk1711

lemma complete_chunk1712 : ∀ i : Fin 200, Compatible (342400 + i.val) →
    (table.lookup (342400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1712 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 342400 342600 :=
  FiniteIntervals.of_fin 342400 200 complete_chunk1712

lemma complete_chunk1713 : ∀ i : Fin 200, Compatible (342600 + i.val) →
    (table.lookup (342600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1713 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 342600 342800 :=
  FiniteIntervals.of_fin 342600 200 complete_chunk1713

lemma complete_chunk1714 : ∀ i : Fin 200, Compatible (342800 + i.val) →
    (table.lookup (342800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1714 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 342800 343000 :=
  FiniteIntervals.of_fin 342800 200 complete_chunk1714

lemma complete_chunk1715 : ∀ i : Fin 200, Compatible (343000 + i.val) →
    (table.lookup (343000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1715 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 343000 343200 :=
  FiniteIntervals.of_fin 343000 200 complete_chunk1715

lemma complete_chunk1716 : ∀ i : Fin 200, Compatible (343200 + i.val) →
    (table.lookup (343200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1716 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 343200 343400 :=
  FiniteIntervals.of_fin 343200 200 complete_chunk1716

lemma complete_chunk1717 : ∀ i : Fin 200, Compatible (343400 + i.val) →
    (table.lookup (343400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1717 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 343400 343600 :=
  FiniteIntervals.of_fin 343400 200 complete_chunk1717

lemma complete_chunk1718 : ∀ i : Fin 200, Compatible (343600 + i.val) →
    (table.lookup (343600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1718 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 343600 343800 :=
  FiniteIntervals.of_fin 343600 200 complete_chunk1718

lemma complete_chunk1719 : ∀ i : Fin 200, Compatible (343800 + i.val) →
    (table.lookup (343800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1719 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 343800 344000 :=
  FiniteIntervals.of_fin 343800 200 complete_chunk1719

#print axioms interval_chunk1710
end Erdos184Work.PureFiveFilter4
