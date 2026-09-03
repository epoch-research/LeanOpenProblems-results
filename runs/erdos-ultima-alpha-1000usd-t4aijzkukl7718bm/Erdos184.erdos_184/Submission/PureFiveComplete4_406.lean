import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4060 : ∀ i : Fin 200, Compatible (812000 + i.val) →
    (table.lookup (812000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4060 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 812000 812200 :=
  FiniteIntervals.of_fin 812000 200 complete_chunk4060

lemma complete_chunk4061 : ∀ i : Fin 200, Compatible (812200 + i.val) →
    (table.lookup (812200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4061 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 812200 812400 :=
  FiniteIntervals.of_fin 812200 200 complete_chunk4061

lemma complete_chunk4062 : ∀ i : Fin 200, Compatible (812400 + i.val) →
    (table.lookup (812400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4062 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 812400 812600 :=
  FiniteIntervals.of_fin 812400 200 complete_chunk4062

lemma complete_chunk4063 : ∀ i : Fin 200, Compatible (812600 + i.val) →
    (table.lookup (812600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4063 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 812600 812800 :=
  FiniteIntervals.of_fin 812600 200 complete_chunk4063

lemma complete_chunk4064 : ∀ i : Fin 200, Compatible (812800 + i.val) →
    (table.lookup (812800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4064 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 812800 813000 :=
  FiniteIntervals.of_fin 812800 200 complete_chunk4064

lemma complete_chunk4065 : ∀ i : Fin 200, Compatible (813000 + i.val) →
    (table.lookup (813000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4065 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 813000 813200 :=
  FiniteIntervals.of_fin 813000 200 complete_chunk4065

lemma complete_chunk4066 : ∀ i : Fin 200, Compatible (813200 + i.val) →
    (table.lookup (813200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4066 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 813200 813400 :=
  FiniteIntervals.of_fin 813200 200 complete_chunk4066

lemma complete_chunk4067 : ∀ i : Fin 200, Compatible (813400 + i.val) →
    (table.lookup (813400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4067 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 813400 813600 :=
  FiniteIntervals.of_fin 813400 200 complete_chunk4067

lemma complete_chunk4068 : ∀ i : Fin 200, Compatible (813600 + i.val) →
    (table.lookup (813600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4068 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 813600 813800 :=
  FiniteIntervals.of_fin 813600 200 complete_chunk4068

lemma complete_chunk4069 : ∀ i : Fin 200, Compatible (813800 + i.val) →
    (table.lookup (813800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4069 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 813800 814000 :=
  FiniteIntervals.of_fin 813800 200 complete_chunk4069

#print axioms interval_chunk4060
end Erdos184Work.PureFiveFilter4
