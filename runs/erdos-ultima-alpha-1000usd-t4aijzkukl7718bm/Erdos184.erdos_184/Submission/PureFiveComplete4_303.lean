import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3030 : ∀ i : Fin 200, Compatible (606000 + i.val) →
    (table.lookup (606000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3030 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 606000 606200 :=
  FiniteIntervals.of_fin 606000 200 complete_chunk3030

lemma complete_chunk3031 : ∀ i : Fin 200, Compatible (606200 + i.val) →
    (table.lookup (606200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3031 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 606200 606400 :=
  FiniteIntervals.of_fin 606200 200 complete_chunk3031

lemma complete_chunk3032 : ∀ i : Fin 200, Compatible (606400 + i.val) →
    (table.lookup (606400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3032 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 606400 606600 :=
  FiniteIntervals.of_fin 606400 200 complete_chunk3032

lemma complete_chunk3033 : ∀ i : Fin 200, Compatible (606600 + i.val) →
    (table.lookup (606600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3033 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 606600 606800 :=
  FiniteIntervals.of_fin 606600 200 complete_chunk3033

lemma complete_chunk3034 : ∀ i : Fin 200, Compatible (606800 + i.val) →
    (table.lookup (606800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3034 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 606800 607000 :=
  FiniteIntervals.of_fin 606800 200 complete_chunk3034

lemma complete_chunk3035 : ∀ i : Fin 200, Compatible (607000 + i.val) →
    (table.lookup (607000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3035 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 607000 607200 :=
  FiniteIntervals.of_fin 607000 200 complete_chunk3035

lemma complete_chunk3036 : ∀ i : Fin 200, Compatible (607200 + i.val) →
    (table.lookup (607200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3036 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 607200 607400 :=
  FiniteIntervals.of_fin 607200 200 complete_chunk3036

lemma complete_chunk3037 : ∀ i : Fin 200, Compatible (607400 + i.val) →
    (table.lookup (607400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3037 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 607400 607600 :=
  FiniteIntervals.of_fin 607400 200 complete_chunk3037

lemma complete_chunk3038 : ∀ i : Fin 200, Compatible (607600 + i.val) →
    (table.lookup (607600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3038 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 607600 607800 :=
  FiniteIntervals.of_fin 607600 200 complete_chunk3038

lemma complete_chunk3039 : ∀ i : Fin 200, Compatible (607800 + i.val) →
    (table.lookup (607800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3039 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 607800 608000 :=
  FiniteIntervals.of_fin 607800 200 complete_chunk3039

#print axioms interval_chunk3030
end Erdos184Work.PureFiveFilter4
