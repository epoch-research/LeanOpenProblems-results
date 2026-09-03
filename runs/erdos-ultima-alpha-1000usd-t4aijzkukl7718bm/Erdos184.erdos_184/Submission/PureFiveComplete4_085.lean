import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk850 : ∀ i : Fin 200, Compatible (170000 + i.val) →
    (table.lookup (170000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk850 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 170000 170200 :=
  FiniteIntervals.of_fin 170000 200 complete_chunk850

lemma complete_chunk851 : ∀ i : Fin 200, Compatible (170200 + i.val) →
    (table.lookup (170200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk851 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 170200 170400 :=
  FiniteIntervals.of_fin 170200 200 complete_chunk851

lemma complete_chunk852 : ∀ i : Fin 200, Compatible (170400 + i.val) →
    (table.lookup (170400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk852 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 170400 170600 :=
  FiniteIntervals.of_fin 170400 200 complete_chunk852

lemma complete_chunk853 : ∀ i : Fin 200, Compatible (170600 + i.val) →
    (table.lookup (170600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk853 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 170600 170800 :=
  FiniteIntervals.of_fin 170600 200 complete_chunk853

lemma complete_chunk854 : ∀ i : Fin 200, Compatible (170800 + i.val) →
    (table.lookup (170800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk854 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 170800 171000 :=
  FiniteIntervals.of_fin 170800 200 complete_chunk854

lemma complete_chunk855 : ∀ i : Fin 200, Compatible (171000 + i.val) →
    (table.lookup (171000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk855 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 171000 171200 :=
  FiniteIntervals.of_fin 171000 200 complete_chunk855

lemma complete_chunk856 : ∀ i : Fin 200, Compatible (171200 + i.val) →
    (table.lookup (171200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk856 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 171200 171400 :=
  FiniteIntervals.of_fin 171200 200 complete_chunk856

lemma complete_chunk857 : ∀ i : Fin 200, Compatible (171400 + i.val) →
    (table.lookup (171400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk857 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 171400 171600 :=
  FiniteIntervals.of_fin 171400 200 complete_chunk857

lemma complete_chunk858 : ∀ i : Fin 200, Compatible (171600 + i.val) →
    (table.lookup (171600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk858 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 171600 171800 :=
  FiniteIntervals.of_fin 171600 200 complete_chunk858

lemma complete_chunk859 : ∀ i : Fin 200, Compatible (171800 + i.val) →
    (table.lookup (171800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk859 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 171800 172000 :=
  FiniteIntervals.of_fin 171800 200 complete_chunk859

#print axioms interval_chunk850
end Erdos184Work.PureFiveFilter4
