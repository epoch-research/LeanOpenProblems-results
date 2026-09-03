import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk60 : ∀ i : Fin 200, Compatible (12000 + i.val) →
    (table.lookup (12000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk60 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 12000 12200 :=
  FiniteIntervals.of_fin 12000 200 complete_chunk60

lemma complete_chunk61 : ∀ i : Fin 200, Compatible (12200 + i.val) →
    (table.lookup (12200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk61 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 12200 12400 :=
  FiniteIntervals.of_fin 12200 200 complete_chunk61

lemma complete_chunk62 : ∀ i : Fin 200, Compatible (12400 + i.val) →
    (table.lookup (12400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk62 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 12400 12600 :=
  FiniteIntervals.of_fin 12400 200 complete_chunk62

lemma complete_chunk63 : ∀ i : Fin 200, Compatible (12600 + i.val) →
    (table.lookup (12600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk63 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 12600 12800 :=
  FiniteIntervals.of_fin 12600 200 complete_chunk63

lemma complete_chunk64 : ∀ i : Fin 200, Compatible (12800 + i.val) →
    (table.lookup (12800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk64 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 12800 13000 :=
  FiniteIntervals.of_fin 12800 200 complete_chunk64

lemma complete_chunk65 : ∀ i : Fin 200, Compatible (13000 + i.val) →
    (table.lookup (13000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk65 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 13000 13200 :=
  FiniteIntervals.of_fin 13000 200 complete_chunk65

lemma complete_chunk66 : ∀ i : Fin 200, Compatible (13200 + i.val) →
    (table.lookup (13200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk66 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 13200 13400 :=
  FiniteIntervals.of_fin 13200 200 complete_chunk66

lemma complete_chunk67 : ∀ i : Fin 200, Compatible (13400 + i.val) →
    (table.lookup (13400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk67 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 13400 13600 :=
  FiniteIntervals.of_fin 13400 200 complete_chunk67

lemma complete_chunk68 : ∀ i : Fin 200, Compatible (13600 + i.val) →
    (table.lookup (13600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk68 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 13600 13800 :=
  FiniteIntervals.of_fin 13600 200 complete_chunk68

lemma complete_chunk69 : ∀ i : Fin 200, Compatible (13800 + i.val) →
    (table.lookup (13800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk69 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 13800 14000 :=
  FiniteIntervals.of_fin 13800 200 complete_chunk69

#print axioms interval_chunk60
end Erdos184Work.PureFiveFilter3
