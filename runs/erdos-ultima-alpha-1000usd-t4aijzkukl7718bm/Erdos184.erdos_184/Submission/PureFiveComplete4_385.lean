import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3850 : ∀ i : Fin 200, Compatible (770000 + i.val) →
    (table.lookup (770000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3850 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 770000 770200 :=
  FiniteIntervals.of_fin 770000 200 complete_chunk3850

lemma complete_chunk3851 : ∀ i : Fin 200, Compatible (770200 + i.val) →
    (table.lookup (770200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3851 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 770200 770400 :=
  FiniteIntervals.of_fin 770200 200 complete_chunk3851

lemma complete_chunk3852 : ∀ i : Fin 200, Compatible (770400 + i.val) →
    (table.lookup (770400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3852 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 770400 770600 :=
  FiniteIntervals.of_fin 770400 200 complete_chunk3852

lemma complete_chunk3853 : ∀ i : Fin 200, Compatible (770600 + i.val) →
    (table.lookup (770600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3853 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 770600 770800 :=
  FiniteIntervals.of_fin 770600 200 complete_chunk3853

lemma complete_chunk3854 : ∀ i : Fin 200, Compatible (770800 + i.val) →
    (table.lookup (770800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3854 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 770800 771000 :=
  FiniteIntervals.of_fin 770800 200 complete_chunk3854

lemma complete_chunk3855 : ∀ i : Fin 200, Compatible (771000 + i.val) →
    (table.lookup (771000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3855 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 771000 771200 :=
  FiniteIntervals.of_fin 771000 200 complete_chunk3855

lemma complete_chunk3856 : ∀ i : Fin 200, Compatible (771200 + i.val) →
    (table.lookup (771200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3856 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 771200 771400 :=
  FiniteIntervals.of_fin 771200 200 complete_chunk3856

lemma complete_chunk3857 : ∀ i : Fin 200, Compatible (771400 + i.val) →
    (table.lookup (771400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3857 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 771400 771600 :=
  FiniteIntervals.of_fin 771400 200 complete_chunk3857

lemma complete_chunk3858 : ∀ i : Fin 200, Compatible (771600 + i.val) →
    (table.lookup (771600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3858 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 771600 771800 :=
  FiniteIntervals.of_fin 771600 200 complete_chunk3858

lemma complete_chunk3859 : ∀ i : Fin 200, Compatible (771800 + i.val) →
    (table.lookup (771800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3859 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 771800 772000 :=
  FiniteIntervals.of_fin 771800 200 complete_chunk3859

#print axioms interval_chunk3850
end Erdos184Work.PureFiveFilter4
