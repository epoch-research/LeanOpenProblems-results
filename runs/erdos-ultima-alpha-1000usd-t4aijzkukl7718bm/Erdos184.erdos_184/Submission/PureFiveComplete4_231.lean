import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2310 : ∀ i : Fin 200, Compatible (462000 + i.val) →
    (table.lookup (462000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2310 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 462000 462200 :=
  FiniteIntervals.of_fin 462000 200 complete_chunk2310

lemma complete_chunk2311 : ∀ i : Fin 200, Compatible (462200 + i.val) →
    (table.lookup (462200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2311 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 462200 462400 :=
  FiniteIntervals.of_fin 462200 200 complete_chunk2311

lemma complete_chunk2312 : ∀ i : Fin 200, Compatible (462400 + i.val) →
    (table.lookup (462400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2312 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 462400 462600 :=
  FiniteIntervals.of_fin 462400 200 complete_chunk2312

lemma complete_chunk2313 : ∀ i : Fin 200, Compatible (462600 + i.val) →
    (table.lookup (462600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2313 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 462600 462800 :=
  FiniteIntervals.of_fin 462600 200 complete_chunk2313

lemma complete_chunk2314 : ∀ i : Fin 200, Compatible (462800 + i.val) →
    (table.lookup (462800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2314 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 462800 463000 :=
  FiniteIntervals.of_fin 462800 200 complete_chunk2314

lemma complete_chunk2315 : ∀ i : Fin 200, Compatible (463000 + i.val) →
    (table.lookup (463000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2315 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 463000 463200 :=
  FiniteIntervals.of_fin 463000 200 complete_chunk2315

lemma complete_chunk2316 : ∀ i : Fin 200, Compatible (463200 + i.val) →
    (table.lookup (463200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2316 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 463200 463400 :=
  FiniteIntervals.of_fin 463200 200 complete_chunk2316

lemma complete_chunk2317 : ∀ i : Fin 200, Compatible (463400 + i.val) →
    (table.lookup (463400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2317 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 463400 463600 :=
  FiniteIntervals.of_fin 463400 200 complete_chunk2317

lemma complete_chunk2318 : ∀ i : Fin 200, Compatible (463600 + i.val) →
    (table.lookup (463600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2318 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 463600 463800 :=
  FiniteIntervals.of_fin 463600 200 complete_chunk2318

lemma complete_chunk2319 : ∀ i : Fin 200, Compatible (463800 + i.val) →
    (table.lookup (463800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2319 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 463800 464000 :=
  FiniteIntervals.of_fin 463800 200 complete_chunk2319

#print axioms interval_chunk2310
end Erdos184Work.PureFiveFilter4
