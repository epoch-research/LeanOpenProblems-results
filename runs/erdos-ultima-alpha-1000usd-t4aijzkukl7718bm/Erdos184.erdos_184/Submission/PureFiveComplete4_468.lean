import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4680 : ∀ i : Fin 200, Compatible (936000 + i.val) →
    (table.lookup (936000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4680 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 936000 936200 :=
  FiniteIntervals.of_fin 936000 200 complete_chunk4680

lemma complete_chunk4681 : ∀ i : Fin 200, Compatible (936200 + i.val) →
    (table.lookup (936200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4681 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 936200 936400 :=
  FiniteIntervals.of_fin 936200 200 complete_chunk4681

lemma complete_chunk4682 : ∀ i : Fin 200, Compatible (936400 + i.val) →
    (table.lookup (936400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4682 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 936400 936600 :=
  FiniteIntervals.of_fin 936400 200 complete_chunk4682

lemma complete_chunk4683 : ∀ i : Fin 200, Compatible (936600 + i.val) →
    (table.lookup (936600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4683 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 936600 936800 :=
  FiniteIntervals.of_fin 936600 200 complete_chunk4683

lemma complete_chunk4684 : ∀ i : Fin 200, Compatible (936800 + i.val) →
    (table.lookup (936800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4684 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 936800 937000 :=
  FiniteIntervals.of_fin 936800 200 complete_chunk4684

lemma complete_chunk4685 : ∀ i : Fin 200, Compatible (937000 + i.val) →
    (table.lookup (937000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4685 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 937000 937200 :=
  FiniteIntervals.of_fin 937000 200 complete_chunk4685

lemma complete_chunk4686 : ∀ i : Fin 200, Compatible (937200 + i.val) →
    (table.lookup (937200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4686 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 937200 937400 :=
  FiniteIntervals.of_fin 937200 200 complete_chunk4686

lemma complete_chunk4687 : ∀ i : Fin 200, Compatible (937400 + i.val) →
    (table.lookup (937400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4687 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 937400 937600 :=
  FiniteIntervals.of_fin 937400 200 complete_chunk4687

lemma complete_chunk4688 : ∀ i : Fin 200, Compatible (937600 + i.val) →
    (table.lookup (937600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4688 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 937600 937800 :=
  FiniteIntervals.of_fin 937600 200 complete_chunk4688

lemma complete_chunk4689 : ∀ i : Fin 200, Compatible (937800 + i.val) →
    (table.lookup (937800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4689 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 937800 938000 :=
  FiniteIntervals.of_fin 937800 200 complete_chunk4689

#print axioms interval_chunk4680
end Erdos184Work.PureFiveFilter4
