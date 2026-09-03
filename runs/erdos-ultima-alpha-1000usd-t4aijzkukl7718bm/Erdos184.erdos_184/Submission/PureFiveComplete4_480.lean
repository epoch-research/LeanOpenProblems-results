import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4800 : ∀ i : Fin 200, Compatible (960000 + i.val) →
    (table.lookup (960000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4800 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 960000 960200 :=
  FiniteIntervals.of_fin 960000 200 complete_chunk4800

lemma complete_chunk4801 : ∀ i : Fin 200, Compatible (960200 + i.val) →
    (table.lookup (960200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4801 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 960200 960400 :=
  FiniteIntervals.of_fin 960200 200 complete_chunk4801

lemma complete_chunk4802 : ∀ i : Fin 200, Compatible (960400 + i.val) →
    (table.lookup (960400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4802 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 960400 960600 :=
  FiniteIntervals.of_fin 960400 200 complete_chunk4802

lemma complete_chunk4803 : ∀ i : Fin 200, Compatible (960600 + i.val) →
    (table.lookup (960600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4803 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 960600 960800 :=
  FiniteIntervals.of_fin 960600 200 complete_chunk4803

lemma complete_chunk4804 : ∀ i : Fin 200, Compatible (960800 + i.val) →
    (table.lookup (960800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4804 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 960800 961000 :=
  FiniteIntervals.of_fin 960800 200 complete_chunk4804

lemma complete_chunk4805 : ∀ i : Fin 200, Compatible (961000 + i.val) →
    (table.lookup (961000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4805 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 961000 961200 :=
  FiniteIntervals.of_fin 961000 200 complete_chunk4805

lemma complete_chunk4806 : ∀ i : Fin 200, Compatible (961200 + i.val) →
    (table.lookup (961200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4806 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 961200 961400 :=
  FiniteIntervals.of_fin 961200 200 complete_chunk4806

lemma complete_chunk4807 : ∀ i : Fin 200, Compatible (961400 + i.val) →
    (table.lookup (961400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4807 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 961400 961600 :=
  FiniteIntervals.of_fin 961400 200 complete_chunk4807

lemma complete_chunk4808 : ∀ i : Fin 200, Compatible (961600 + i.val) →
    (table.lookup (961600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4808 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 961600 961800 :=
  FiniteIntervals.of_fin 961600 200 complete_chunk4808

lemma complete_chunk4809 : ∀ i : Fin 200, Compatible (961800 + i.val) →
    (table.lookup (961800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4809 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 961800 962000 :=
  FiniteIntervals.of_fin 961800 200 complete_chunk4809

#print axioms interval_chunk4800
end Erdos184Work.PureFiveFilter4
