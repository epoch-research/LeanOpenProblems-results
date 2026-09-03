import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4090 : ∀ i : Fin 200, Compatible (818000 + i.val) →
    (table.lookup (818000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4090 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 818000 818200 :=
  FiniteIntervals.of_fin 818000 200 complete_chunk4090

lemma complete_chunk4091 : ∀ i : Fin 200, Compatible (818200 + i.val) →
    (table.lookup (818200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4091 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 818200 818400 :=
  FiniteIntervals.of_fin 818200 200 complete_chunk4091

lemma complete_chunk4092 : ∀ i : Fin 200, Compatible (818400 + i.val) →
    (table.lookup (818400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4092 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 818400 818600 :=
  FiniteIntervals.of_fin 818400 200 complete_chunk4092

lemma complete_chunk4093 : ∀ i : Fin 200, Compatible (818600 + i.val) →
    (table.lookup (818600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4093 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 818600 818800 :=
  FiniteIntervals.of_fin 818600 200 complete_chunk4093

lemma complete_chunk4094 : ∀ i : Fin 200, Compatible (818800 + i.val) →
    (table.lookup (818800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4094 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 818800 819000 :=
  FiniteIntervals.of_fin 818800 200 complete_chunk4094

lemma complete_chunk4095 : ∀ i : Fin 200, Compatible (819000 + i.val) →
    (table.lookup (819000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4095 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 819000 819200 :=
  FiniteIntervals.of_fin 819000 200 complete_chunk4095

lemma complete_chunk4096 : ∀ i : Fin 200, Compatible (819200 + i.val) →
    (table.lookup (819200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4096 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 819200 819400 :=
  FiniteIntervals.of_fin 819200 200 complete_chunk4096

lemma complete_chunk4097 : ∀ i : Fin 200, Compatible (819400 + i.val) →
    (table.lookup (819400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4097 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 819400 819600 :=
  FiniteIntervals.of_fin 819400 200 complete_chunk4097

lemma complete_chunk4098 : ∀ i : Fin 200, Compatible (819600 + i.val) →
    (table.lookup (819600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4098 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 819600 819800 :=
  FiniteIntervals.of_fin 819600 200 complete_chunk4098

lemma complete_chunk4099 : ∀ i : Fin 200, Compatible (819800 + i.val) →
    (table.lookup (819800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4099 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 819800 820000 :=
  FiniteIntervals.of_fin 819800 200 complete_chunk4099

#print axioms interval_chunk4090
end Erdos184Work.PureFiveFilter4
