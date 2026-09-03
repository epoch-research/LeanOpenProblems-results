import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk230 : ∀ i : Fin 200, Compatible (46000 + i.val) →
    (table.lookup (46000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk230 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 46000 46200 :=
  FiniteIntervals.of_fin 46000 200 complete_chunk230

lemma complete_chunk231 : ∀ i : Fin 200, Compatible (46200 + i.val) →
    (table.lookup (46200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk231 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 46200 46400 :=
  FiniteIntervals.of_fin 46200 200 complete_chunk231

lemma complete_chunk232 : ∀ i : Fin 200, Compatible (46400 + i.val) →
    (table.lookup (46400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk232 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 46400 46600 :=
  FiniteIntervals.of_fin 46400 200 complete_chunk232

lemma complete_chunk233 : ∀ i : Fin 200, Compatible (46600 + i.val) →
    (table.lookup (46600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk233 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 46600 46800 :=
  FiniteIntervals.of_fin 46600 200 complete_chunk233

lemma complete_chunk234 : ∀ i : Fin 200, Compatible (46800 + i.val) →
    (table.lookup (46800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk234 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 46800 47000 :=
  FiniteIntervals.of_fin 46800 200 complete_chunk234

lemma complete_chunk235 : ∀ i : Fin 200, Compatible (47000 + i.val) →
    (table.lookup (47000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk235 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 47000 47200 :=
  FiniteIntervals.of_fin 47000 200 complete_chunk235

lemma complete_chunk236 : ∀ i : Fin 200, Compatible (47200 + i.val) →
    (table.lookup (47200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk236 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 47200 47400 :=
  FiniteIntervals.of_fin 47200 200 complete_chunk236

lemma complete_chunk237 : ∀ i : Fin 200, Compatible (47400 + i.val) →
    (table.lookup (47400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk237 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 47400 47600 :=
  FiniteIntervals.of_fin 47400 200 complete_chunk237

lemma complete_chunk238 : ∀ i : Fin 200, Compatible (47600 + i.val) →
    (table.lookup (47600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk238 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 47600 47800 :=
  FiniteIntervals.of_fin 47600 200 complete_chunk238

lemma complete_chunk239 : ∀ i : Fin 200, Compatible (47800 + i.val) →
    (table.lookup (47800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk239 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 47800 48000 :=
  FiniteIntervals.of_fin 47800 200 complete_chunk239

#print axioms interval_chunk230
end Erdos184Work.PureFiveFilter3
