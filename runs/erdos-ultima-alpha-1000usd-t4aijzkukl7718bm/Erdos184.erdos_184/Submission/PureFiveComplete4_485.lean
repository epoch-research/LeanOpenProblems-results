import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4850 : ∀ i : Fin 200, Compatible (970000 + i.val) →
    (table.lookup (970000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4850 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 970000 970200 :=
  FiniteIntervals.of_fin 970000 200 complete_chunk4850

lemma complete_chunk4851 : ∀ i : Fin 200, Compatible (970200 + i.val) →
    (table.lookup (970200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4851 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 970200 970400 :=
  FiniteIntervals.of_fin 970200 200 complete_chunk4851

lemma complete_chunk4852 : ∀ i : Fin 200, Compatible (970400 + i.val) →
    (table.lookup (970400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4852 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 970400 970600 :=
  FiniteIntervals.of_fin 970400 200 complete_chunk4852

lemma complete_chunk4853 : ∀ i : Fin 200, Compatible (970600 + i.val) →
    (table.lookup (970600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4853 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 970600 970800 :=
  FiniteIntervals.of_fin 970600 200 complete_chunk4853

lemma complete_chunk4854 : ∀ i : Fin 200, Compatible (970800 + i.val) →
    (table.lookup (970800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4854 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 970800 971000 :=
  FiniteIntervals.of_fin 970800 200 complete_chunk4854

lemma complete_chunk4855 : ∀ i : Fin 200, Compatible (971000 + i.val) →
    (table.lookup (971000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4855 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 971000 971200 :=
  FiniteIntervals.of_fin 971000 200 complete_chunk4855

lemma complete_chunk4856 : ∀ i : Fin 200, Compatible (971200 + i.val) →
    (table.lookup (971200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4856 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 971200 971400 :=
  FiniteIntervals.of_fin 971200 200 complete_chunk4856

lemma complete_chunk4857 : ∀ i : Fin 200, Compatible (971400 + i.val) →
    (table.lookup (971400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4857 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 971400 971600 :=
  FiniteIntervals.of_fin 971400 200 complete_chunk4857

lemma complete_chunk4858 : ∀ i : Fin 200, Compatible (971600 + i.val) →
    (table.lookup (971600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4858 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 971600 971800 :=
  FiniteIntervals.of_fin 971600 200 complete_chunk4858

lemma complete_chunk4859 : ∀ i : Fin 200, Compatible (971800 + i.val) →
    (table.lookup (971800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4859 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 971800 972000 :=
  FiniteIntervals.of_fin 971800 200 complete_chunk4859

#print axioms interval_chunk4850
end Erdos184Work.PureFiveFilter4
