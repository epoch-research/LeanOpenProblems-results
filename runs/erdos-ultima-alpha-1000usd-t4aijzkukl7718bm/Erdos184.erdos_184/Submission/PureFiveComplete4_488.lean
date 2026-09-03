import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4880 : ∀ i : Fin 200, Compatible (976000 + i.val) →
    (table.lookup (976000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4880 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 976000 976200 :=
  FiniteIntervals.of_fin 976000 200 complete_chunk4880

lemma complete_chunk4881 : ∀ i : Fin 200, Compatible (976200 + i.val) →
    (table.lookup (976200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4881 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 976200 976400 :=
  FiniteIntervals.of_fin 976200 200 complete_chunk4881

lemma complete_chunk4882 : ∀ i : Fin 200, Compatible (976400 + i.val) →
    (table.lookup (976400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4882 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 976400 976600 :=
  FiniteIntervals.of_fin 976400 200 complete_chunk4882

lemma complete_chunk4883 : ∀ i : Fin 200, Compatible (976600 + i.val) →
    (table.lookup (976600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4883 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 976600 976800 :=
  FiniteIntervals.of_fin 976600 200 complete_chunk4883

lemma complete_chunk4884 : ∀ i : Fin 200, Compatible (976800 + i.val) →
    (table.lookup (976800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4884 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 976800 977000 :=
  FiniteIntervals.of_fin 976800 200 complete_chunk4884

lemma complete_chunk4885 : ∀ i : Fin 200, Compatible (977000 + i.val) →
    (table.lookup (977000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4885 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 977000 977200 :=
  FiniteIntervals.of_fin 977000 200 complete_chunk4885

lemma complete_chunk4886 : ∀ i : Fin 200, Compatible (977200 + i.val) →
    (table.lookup (977200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4886 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 977200 977400 :=
  FiniteIntervals.of_fin 977200 200 complete_chunk4886

lemma complete_chunk4887 : ∀ i : Fin 200, Compatible (977400 + i.val) →
    (table.lookup (977400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4887 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 977400 977600 :=
  FiniteIntervals.of_fin 977400 200 complete_chunk4887

lemma complete_chunk4888 : ∀ i : Fin 200, Compatible (977600 + i.val) →
    (table.lookup (977600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4888 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 977600 977800 :=
  FiniteIntervals.of_fin 977600 200 complete_chunk4888

lemma complete_chunk4889 : ∀ i : Fin 200, Compatible (977800 + i.val) →
    (table.lookup (977800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4889 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 977800 978000 :=
  FiniteIntervals.of_fin 977800 200 complete_chunk4889

#print axioms interval_chunk4880
end Erdos184Work.PureFiveFilter4
