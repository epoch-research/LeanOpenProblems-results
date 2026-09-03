import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2240 : ∀ i : Fin 200, Compatible (448000 + i.val) →
    (table.lookup (448000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2240 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 448000 448200 :=
  FiniteIntervals.of_fin 448000 200 complete_chunk2240

lemma complete_chunk2241 : ∀ i : Fin 200, Compatible (448200 + i.val) →
    (table.lookup (448200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2241 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 448200 448400 :=
  FiniteIntervals.of_fin 448200 200 complete_chunk2241

lemma complete_chunk2242 : ∀ i : Fin 200, Compatible (448400 + i.val) →
    (table.lookup (448400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2242 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 448400 448600 :=
  FiniteIntervals.of_fin 448400 200 complete_chunk2242

lemma complete_chunk2243 : ∀ i : Fin 200, Compatible (448600 + i.val) →
    (table.lookup (448600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2243 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 448600 448800 :=
  FiniteIntervals.of_fin 448600 200 complete_chunk2243

lemma complete_chunk2244 : ∀ i : Fin 200, Compatible (448800 + i.val) →
    (table.lookup (448800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2244 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 448800 449000 :=
  FiniteIntervals.of_fin 448800 200 complete_chunk2244

lemma complete_chunk2245 : ∀ i : Fin 200, Compatible (449000 + i.val) →
    (table.lookup (449000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2245 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 449000 449200 :=
  FiniteIntervals.of_fin 449000 200 complete_chunk2245

lemma complete_chunk2246 : ∀ i : Fin 200, Compatible (449200 + i.val) →
    (table.lookup (449200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2246 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 449200 449400 :=
  FiniteIntervals.of_fin 449200 200 complete_chunk2246

lemma complete_chunk2247 : ∀ i : Fin 200, Compatible (449400 + i.val) →
    (table.lookup (449400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2247 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 449400 449600 :=
  FiniteIntervals.of_fin 449400 200 complete_chunk2247

lemma complete_chunk2248 : ∀ i : Fin 200, Compatible (449600 + i.val) →
    (table.lookup (449600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2248 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 449600 449800 :=
  FiniteIntervals.of_fin 449600 200 complete_chunk2248

lemma complete_chunk2249 : ∀ i : Fin 200, Compatible (449800 + i.val) →
    (table.lookup (449800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2249 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 449800 450000 :=
  FiniteIntervals.of_fin 449800 200 complete_chunk2249

#print axioms interval_chunk2240
end Erdos184Work.PureFiveFilter4
