import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2710 : ∀ i : Fin 200, Compatible (542000 + i.val) →
    (table.lookup (542000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2710 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 542000 542200 :=
  FiniteIntervals.of_fin 542000 200 complete_chunk2710

lemma complete_chunk2711 : ∀ i : Fin 200, Compatible (542200 + i.val) →
    (table.lookup (542200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2711 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 542200 542400 :=
  FiniteIntervals.of_fin 542200 200 complete_chunk2711

lemma complete_chunk2712 : ∀ i : Fin 200, Compatible (542400 + i.val) →
    (table.lookup (542400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2712 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 542400 542600 :=
  FiniteIntervals.of_fin 542400 200 complete_chunk2712

lemma complete_chunk2713 : ∀ i : Fin 200, Compatible (542600 + i.val) →
    (table.lookup (542600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2713 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 542600 542800 :=
  FiniteIntervals.of_fin 542600 200 complete_chunk2713

lemma complete_chunk2714 : ∀ i : Fin 200, Compatible (542800 + i.val) →
    (table.lookup (542800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2714 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 542800 543000 :=
  FiniteIntervals.of_fin 542800 200 complete_chunk2714

lemma complete_chunk2715 : ∀ i : Fin 200, Compatible (543000 + i.val) →
    (table.lookup (543000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2715 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 543000 543200 :=
  FiniteIntervals.of_fin 543000 200 complete_chunk2715

lemma complete_chunk2716 : ∀ i : Fin 200, Compatible (543200 + i.val) →
    (table.lookup (543200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2716 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 543200 543400 :=
  FiniteIntervals.of_fin 543200 200 complete_chunk2716

lemma complete_chunk2717 : ∀ i : Fin 200, Compatible (543400 + i.val) →
    (table.lookup (543400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2717 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 543400 543600 :=
  FiniteIntervals.of_fin 543400 200 complete_chunk2717

lemma complete_chunk2718 : ∀ i : Fin 200, Compatible (543600 + i.val) →
    (table.lookup (543600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2718 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 543600 543800 :=
  FiniteIntervals.of_fin 543600 200 complete_chunk2718

lemma complete_chunk2719 : ∀ i : Fin 200, Compatible (543800 + i.val) →
    (table.lookup (543800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2719 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 543800 544000 :=
  FiniteIntervals.of_fin 543800 200 complete_chunk2719

#print axioms interval_chunk2710
end Erdos184Work.PureFiveFilter4
