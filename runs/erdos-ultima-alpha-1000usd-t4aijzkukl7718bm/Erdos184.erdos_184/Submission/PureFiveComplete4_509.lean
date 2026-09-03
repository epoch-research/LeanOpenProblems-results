import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5090 : ∀ i : Fin 200, Compatible (1018000 + i.val) →
    (table.lookup (1018000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5090 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1018000 1018200 :=
  FiniteIntervals.of_fin 1018000 200 complete_chunk5090

lemma complete_chunk5091 : ∀ i : Fin 200, Compatible (1018200 + i.val) →
    (table.lookup (1018200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5091 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1018200 1018400 :=
  FiniteIntervals.of_fin 1018200 200 complete_chunk5091

lemma complete_chunk5092 : ∀ i : Fin 200, Compatible (1018400 + i.val) →
    (table.lookup (1018400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5092 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1018400 1018600 :=
  FiniteIntervals.of_fin 1018400 200 complete_chunk5092

lemma complete_chunk5093 : ∀ i : Fin 200, Compatible (1018600 + i.val) →
    (table.lookup (1018600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5093 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1018600 1018800 :=
  FiniteIntervals.of_fin 1018600 200 complete_chunk5093

lemma complete_chunk5094 : ∀ i : Fin 200, Compatible (1018800 + i.val) →
    (table.lookup (1018800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5094 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1018800 1019000 :=
  FiniteIntervals.of_fin 1018800 200 complete_chunk5094

lemma complete_chunk5095 : ∀ i : Fin 200, Compatible (1019000 + i.val) →
    (table.lookup (1019000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5095 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1019000 1019200 :=
  FiniteIntervals.of_fin 1019000 200 complete_chunk5095

lemma complete_chunk5096 : ∀ i : Fin 200, Compatible (1019200 + i.val) →
    (table.lookup (1019200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5096 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1019200 1019400 :=
  FiniteIntervals.of_fin 1019200 200 complete_chunk5096

lemma complete_chunk5097 : ∀ i : Fin 200, Compatible (1019400 + i.val) →
    (table.lookup (1019400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5097 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1019400 1019600 :=
  FiniteIntervals.of_fin 1019400 200 complete_chunk5097

lemma complete_chunk5098 : ∀ i : Fin 200, Compatible (1019600 + i.val) →
    (table.lookup (1019600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5098 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1019600 1019800 :=
  FiniteIntervals.of_fin 1019600 200 complete_chunk5098

lemma complete_chunk5099 : ∀ i : Fin 200, Compatible (1019800 + i.val) →
    (table.lookup (1019800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5099 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1019800 1020000 :=
  FiniteIntervals.of_fin 1019800 200 complete_chunk5099

#print axioms interval_chunk5090
end Erdos184Work.PureFiveFilter4
