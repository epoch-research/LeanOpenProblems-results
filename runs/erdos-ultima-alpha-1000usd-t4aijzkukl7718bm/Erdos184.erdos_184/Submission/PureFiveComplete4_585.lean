import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5850 : ∀ i : Fin 200, Compatible (1170000 + i.val) →
    (table.lookup (1170000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5850 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1170000 1170200 :=
  FiniteIntervals.of_fin 1170000 200 complete_chunk5850

lemma complete_chunk5851 : ∀ i : Fin 200, Compatible (1170200 + i.val) →
    (table.lookup (1170200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5851 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1170200 1170400 :=
  FiniteIntervals.of_fin 1170200 200 complete_chunk5851

lemma complete_chunk5852 : ∀ i : Fin 200, Compatible (1170400 + i.val) →
    (table.lookup (1170400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5852 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1170400 1170600 :=
  FiniteIntervals.of_fin 1170400 200 complete_chunk5852

lemma complete_chunk5853 : ∀ i : Fin 200, Compatible (1170600 + i.val) →
    (table.lookup (1170600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5853 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1170600 1170800 :=
  FiniteIntervals.of_fin 1170600 200 complete_chunk5853

lemma complete_chunk5854 : ∀ i : Fin 200, Compatible (1170800 + i.val) →
    (table.lookup (1170800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5854 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1170800 1171000 :=
  FiniteIntervals.of_fin 1170800 200 complete_chunk5854

lemma complete_chunk5855 : ∀ i : Fin 200, Compatible (1171000 + i.val) →
    (table.lookup (1171000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5855 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1171000 1171200 :=
  FiniteIntervals.of_fin 1171000 200 complete_chunk5855

lemma complete_chunk5856 : ∀ i : Fin 200, Compatible (1171200 + i.val) →
    (table.lookup (1171200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5856 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1171200 1171400 :=
  FiniteIntervals.of_fin 1171200 200 complete_chunk5856

lemma complete_chunk5857 : ∀ i : Fin 200, Compatible (1171400 + i.val) →
    (table.lookup (1171400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5857 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1171400 1171600 :=
  FiniteIntervals.of_fin 1171400 200 complete_chunk5857

lemma complete_chunk5858 : ∀ i : Fin 200, Compatible (1171600 + i.val) →
    (table.lookup (1171600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5858 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1171600 1171800 :=
  FiniteIntervals.of_fin 1171600 200 complete_chunk5858

lemma complete_chunk5859 : ∀ i : Fin 200, Compatible (1171800 + i.val) →
    (table.lookup (1171800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5859 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1171800 1172000 :=
  FiniteIntervals.of_fin 1171800 200 complete_chunk5859

#print axioms interval_chunk5850
end Erdos184Work.PureFiveFilter4
