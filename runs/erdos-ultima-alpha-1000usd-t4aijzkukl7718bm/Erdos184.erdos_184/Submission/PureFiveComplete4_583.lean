import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5830 : ∀ i : Fin 200, Compatible (1166000 + i.val) →
    (table.lookup (1166000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5830 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1166000 1166200 :=
  FiniteIntervals.of_fin 1166000 200 complete_chunk5830

lemma complete_chunk5831 : ∀ i : Fin 200, Compatible (1166200 + i.val) →
    (table.lookup (1166200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5831 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1166200 1166400 :=
  FiniteIntervals.of_fin 1166200 200 complete_chunk5831

lemma complete_chunk5832 : ∀ i : Fin 200, Compatible (1166400 + i.val) →
    (table.lookup (1166400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5832 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1166400 1166600 :=
  FiniteIntervals.of_fin 1166400 200 complete_chunk5832

lemma complete_chunk5833 : ∀ i : Fin 200, Compatible (1166600 + i.val) →
    (table.lookup (1166600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5833 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1166600 1166800 :=
  FiniteIntervals.of_fin 1166600 200 complete_chunk5833

lemma complete_chunk5834 : ∀ i : Fin 200, Compatible (1166800 + i.val) →
    (table.lookup (1166800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5834 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1166800 1167000 :=
  FiniteIntervals.of_fin 1166800 200 complete_chunk5834

lemma complete_chunk5835 : ∀ i : Fin 200, Compatible (1167000 + i.val) →
    (table.lookup (1167000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5835 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1167000 1167200 :=
  FiniteIntervals.of_fin 1167000 200 complete_chunk5835

lemma complete_chunk5836 : ∀ i : Fin 200, Compatible (1167200 + i.val) →
    (table.lookup (1167200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5836 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1167200 1167400 :=
  FiniteIntervals.of_fin 1167200 200 complete_chunk5836

lemma complete_chunk5837 : ∀ i : Fin 200, Compatible (1167400 + i.val) →
    (table.lookup (1167400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5837 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1167400 1167600 :=
  FiniteIntervals.of_fin 1167400 200 complete_chunk5837

lemma complete_chunk5838 : ∀ i : Fin 200, Compatible (1167600 + i.val) →
    (table.lookup (1167600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5838 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1167600 1167800 :=
  FiniteIntervals.of_fin 1167600 200 complete_chunk5838

lemma complete_chunk5839 : ∀ i : Fin 200, Compatible (1167800 + i.val) →
    (table.lookup (1167800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5839 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1167800 1168000 :=
  FiniteIntervals.of_fin 1167800 200 complete_chunk5839

#print axioms interval_chunk5830
end Erdos184Work.PureFiveFilter4
