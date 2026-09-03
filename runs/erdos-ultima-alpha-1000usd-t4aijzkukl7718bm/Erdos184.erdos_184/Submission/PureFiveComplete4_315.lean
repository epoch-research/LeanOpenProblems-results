import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3150 : ∀ i : Fin 200, Compatible (630000 + i.val) →
    (table.lookup (630000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3150 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 630000 630200 :=
  FiniteIntervals.of_fin 630000 200 complete_chunk3150

lemma complete_chunk3151 : ∀ i : Fin 200, Compatible (630200 + i.val) →
    (table.lookup (630200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3151 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 630200 630400 :=
  FiniteIntervals.of_fin 630200 200 complete_chunk3151

lemma complete_chunk3152 : ∀ i : Fin 200, Compatible (630400 + i.val) →
    (table.lookup (630400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3152 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 630400 630600 :=
  FiniteIntervals.of_fin 630400 200 complete_chunk3152

lemma complete_chunk3153 : ∀ i : Fin 200, Compatible (630600 + i.val) →
    (table.lookup (630600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3153 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 630600 630800 :=
  FiniteIntervals.of_fin 630600 200 complete_chunk3153

lemma complete_chunk3154 : ∀ i : Fin 200, Compatible (630800 + i.val) →
    (table.lookup (630800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3154 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 630800 631000 :=
  FiniteIntervals.of_fin 630800 200 complete_chunk3154

lemma complete_chunk3155 : ∀ i : Fin 200, Compatible (631000 + i.val) →
    (table.lookup (631000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3155 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 631000 631200 :=
  FiniteIntervals.of_fin 631000 200 complete_chunk3155

lemma complete_chunk3156 : ∀ i : Fin 200, Compatible (631200 + i.val) →
    (table.lookup (631200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3156 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 631200 631400 :=
  FiniteIntervals.of_fin 631200 200 complete_chunk3156

lemma complete_chunk3157 : ∀ i : Fin 200, Compatible (631400 + i.val) →
    (table.lookup (631400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3157 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 631400 631600 :=
  FiniteIntervals.of_fin 631400 200 complete_chunk3157

lemma complete_chunk3158 : ∀ i : Fin 200, Compatible (631600 + i.val) →
    (table.lookup (631600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3158 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 631600 631800 :=
  FiniteIntervals.of_fin 631600 200 complete_chunk3158

lemma complete_chunk3159 : ∀ i : Fin 200, Compatible (631800 + i.val) →
    (table.lookup (631800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3159 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 631800 632000 :=
  FiniteIntervals.of_fin 631800 200 complete_chunk3159

#print axioms interval_chunk3150
end Erdos184Work.PureFiveFilter4
