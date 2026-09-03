import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3190 : ∀ i : Fin 200, Compatible (638000 + i.val) →
    (table.lookup (638000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3190 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 638000 638200 :=
  FiniteIntervals.of_fin 638000 200 complete_chunk3190

lemma complete_chunk3191 : ∀ i : Fin 200, Compatible (638200 + i.val) →
    (table.lookup (638200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3191 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 638200 638400 :=
  FiniteIntervals.of_fin 638200 200 complete_chunk3191

lemma complete_chunk3192 : ∀ i : Fin 200, Compatible (638400 + i.val) →
    (table.lookup (638400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3192 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 638400 638600 :=
  FiniteIntervals.of_fin 638400 200 complete_chunk3192

lemma complete_chunk3193 : ∀ i : Fin 200, Compatible (638600 + i.val) →
    (table.lookup (638600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3193 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 638600 638800 :=
  FiniteIntervals.of_fin 638600 200 complete_chunk3193

lemma complete_chunk3194 : ∀ i : Fin 200, Compatible (638800 + i.val) →
    (table.lookup (638800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3194 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 638800 639000 :=
  FiniteIntervals.of_fin 638800 200 complete_chunk3194

lemma complete_chunk3195 : ∀ i : Fin 200, Compatible (639000 + i.val) →
    (table.lookup (639000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3195 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 639000 639200 :=
  FiniteIntervals.of_fin 639000 200 complete_chunk3195

lemma complete_chunk3196 : ∀ i : Fin 200, Compatible (639200 + i.val) →
    (table.lookup (639200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3196 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 639200 639400 :=
  FiniteIntervals.of_fin 639200 200 complete_chunk3196

lemma complete_chunk3197 : ∀ i : Fin 200, Compatible (639400 + i.val) →
    (table.lookup (639400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3197 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 639400 639600 :=
  FiniteIntervals.of_fin 639400 200 complete_chunk3197

lemma complete_chunk3198 : ∀ i : Fin 200, Compatible (639600 + i.val) →
    (table.lookup (639600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3198 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 639600 639800 :=
  FiniteIntervals.of_fin 639600 200 complete_chunk3198

lemma complete_chunk3199 : ∀ i : Fin 200, Compatible (639800 + i.val) →
    (table.lookup (639800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3199 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 639800 640000 :=
  FiniteIntervals.of_fin 639800 200 complete_chunk3199

#print axioms interval_chunk3190
end Erdos184Work.PureFiveFilter4
