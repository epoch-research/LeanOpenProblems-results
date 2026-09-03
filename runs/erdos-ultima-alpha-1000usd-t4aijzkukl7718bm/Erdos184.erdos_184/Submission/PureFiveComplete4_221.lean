import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2210 : ∀ i : Fin 200, Compatible (442000 + i.val) →
    (table.lookup (442000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2210 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 442000 442200 :=
  FiniteIntervals.of_fin 442000 200 complete_chunk2210

lemma complete_chunk2211 : ∀ i : Fin 200, Compatible (442200 + i.val) →
    (table.lookup (442200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2211 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 442200 442400 :=
  FiniteIntervals.of_fin 442200 200 complete_chunk2211

lemma complete_chunk2212 : ∀ i : Fin 200, Compatible (442400 + i.val) →
    (table.lookup (442400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2212 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 442400 442600 :=
  FiniteIntervals.of_fin 442400 200 complete_chunk2212

lemma complete_chunk2213 : ∀ i : Fin 200, Compatible (442600 + i.val) →
    (table.lookup (442600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2213 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 442600 442800 :=
  FiniteIntervals.of_fin 442600 200 complete_chunk2213

lemma complete_chunk2214 : ∀ i : Fin 200, Compatible (442800 + i.val) →
    (table.lookup (442800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2214 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 442800 443000 :=
  FiniteIntervals.of_fin 442800 200 complete_chunk2214

lemma complete_chunk2215 : ∀ i : Fin 200, Compatible (443000 + i.val) →
    (table.lookup (443000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2215 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 443000 443200 :=
  FiniteIntervals.of_fin 443000 200 complete_chunk2215

lemma complete_chunk2216 : ∀ i : Fin 200, Compatible (443200 + i.val) →
    (table.lookup (443200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2216 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 443200 443400 :=
  FiniteIntervals.of_fin 443200 200 complete_chunk2216

lemma complete_chunk2217 : ∀ i : Fin 200, Compatible (443400 + i.val) →
    (table.lookup (443400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2217 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 443400 443600 :=
  FiniteIntervals.of_fin 443400 200 complete_chunk2217

lemma complete_chunk2218 : ∀ i : Fin 200, Compatible (443600 + i.val) →
    (table.lookup (443600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2218 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 443600 443800 :=
  FiniteIntervals.of_fin 443600 200 complete_chunk2218

lemma complete_chunk2219 : ∀ i : Fin 200, Compatible (443800 + i.val) →
    (table.lookup (443800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2219 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 443800 444000 :=
  FiniteIntervals.of_fin 443800 200 complete_chunk2219

#print axioms interval_chunk2210
end Erdos184Work.PureFiveFilter4
