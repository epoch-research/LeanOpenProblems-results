import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4990 : ∀ i : Fin 200, Compatible (998000 + i.val) →
    (table.lookup (998000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4990 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 998000 998200 :=
  FiniteIntervals.of_fin 998000 200 complete_chunk4990

lemma complete_chunk4991 : ∀ i : Fin 200, Compatible (998200 + i.val) →
    (table.lookup (998200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4991 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 998200 998400 :=
  FiniteIntervals.of_fin 998200 200 complete_chunk4991

lemma complete_chunk4992 : ∀ i : Fin 200, Compatible (998400 + i.val) →
    (table.lookup (998400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4992 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 998400 998600 :=
  FiniteIntervals.of_fin 998400 200 complete_chunk4992

lemma complete_chunk4993 : ∀ i : Fin 200, Compatible (998600 + i.val) →
    (table.lookup (998600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4993 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 998600 998800 :=
  FiniteIntervals.of_fin 998600 200 complete_chunk4993

lemma complete_chunk4994 : ∀ i : Fin 200, Compatible (998800 + i.val) →
    (table.lookup (998800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4994 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 998800 999000 :=
  FiniteIntervals.of_fin 998800 200 complete_chunk4994

lemma complete_chunk4995 : ∀ i : Fin 200, Compatible (999000 + i.val) →
    (table.lookup (999000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4995 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 999000 999200 :=
  FiniteIntervals.of_fin 999000 200 complete_chunk4995

lemma complete_chunk4996 : ∀ i : Fin 200, Compatible (999200 + i.val) →
    (table.lookup (999200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4996 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 999200 999400 :=
  FiniteIntervals.of_fin 999200 200 complete_chunk4996

lemma complete_chunk4997 : ∀ i : Fin 200, Compatible (999400 + i.val) →
    (table.lookup (999400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4997 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 999400 999600 :=
  FiniteIntervals.of_fin 999400 200 complete_chunk4997

lemma complete_chunk4998 : ∀ i : Fin 200, Compatible (999600 + i.val) →
    (table.lookup (999600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4998 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 999600 999800 :=
  FiniteIntervals.of_fin 999600 200 complete_chunk4998

lemma complete_chunk4999 : ∀ i : Fin 200, Compatible (999800 + i.val) →
    (table.lookup (999800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4999 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 999800 1000000 :=
  FiniteIntervals.of_fin 999800 200 complete_chunk4999

#print axioms interval_chunk4990
end Erdos184Work.PureFiveFilter4
