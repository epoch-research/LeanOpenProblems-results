import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3230 : ∀ i : Fin 200, Compatible (646000 + i.val) →
    (table.lookup (646000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3230 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 646000 646200 :=
  FiniteIntervals.of_fin 646000 200 complete_chunk3230

lemma complete_chunk3231 : ∀ i : Fin 200, Compatible (646200 + i.val) →
    (table.lookup (646200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3231 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 646200 646400 :=
  FiniteIntervals.of_fin 646200 200 complete_chunk3231

lemma complete_chunk3232 : ∀ i : Fin 200, Compatible (646400 + i.val) →
    (table.lookup (646400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3232 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 646400 646600 :=
  FiniteIntervals.of_fin 646400 200 complete_chunk3232

lemma complete_chunk3233 : ∀ i : Fin 200, Compatible (646600 + i.val) →
    (table.lookup (646600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3233 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 646600 646800 :=
  FiniteIntervals.of_fin 646600 200 complete_chunk3233

lemma complete_chunk3234 : ∀ i : Fin 200, Compatible (646800 + i.val) →
    (table.lookup (646800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3234 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 646800 647000 :=
  FiniteIntervals.of_fin 646800 200 complete_chunk3234

lemma complete_chunk3235 : ∀ i : Fin 200, Compatible (647000 + i.val) →
    (table.lookup (647000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3235 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 647000 647200 :=
  FiniteIntervals.of_fin 647000 200 complete_chunk3235

lemma complete_chunk3236 : ∀ i : Fin 200, Compatible (647200 + i.val) →
    (table.lookup (647200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3236 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 647200 647400 :=
  FiniteIntervals.of_fin 647200 200 complete_chunk3236

lemma complete_chunk3237 : ∀ i : Fin 200, Compatible (647400 + i.val) →
    (table.lookup (647400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3237 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 647400 647600 :=
  FiniteIntervals.of_fin 647400 200 complete_chunk3237

lemma complete_chunk3238 : ∀ i : Fin 200, Compatible (647600 + i.val) →
    (table.lookup (647600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3238 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 647600 647800 :=
  FiniteIntervals.of_fin 647600 200 complete_chunk3238

lemma complete_chunk3239 : ∀ i : Fin 200, Compatible (647800 + i.val) →
    (table.lookup (647800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3239 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 647800 648000 :=
  FiniteIntervals.of_fin 647800 200 complete_chunk3239

#print axioms interval_chunk3230
end Erdos184Work.PureFiveFilter4
