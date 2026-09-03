import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2260 : ∀ i : Fin 200, Compatible (452000 + i.val) →
    (table.lookup (452000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2260 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 452000 452200 :=
  FiniteIntervals.of_fin 452000 200 complete_chunk2260

lemma complete_chunk2261 : ∀ i : Fin 200, Compatible (452200 + i.val) →
    (table.lookup (452200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2261 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 452200 452400 :=
  FiniteIntervals.of_fin 452200 200 complete_chunk2261

lemma complete_chunk2262 : ∀ i : Fin 200, Compatible (452400 + i.val) →
    (table.lookup (452400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2262 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 452400 452600 :=
  FiniteIntervals.of_fin 452400 200 complete_chunk2262

lemma complete_chunk2263 : ∀ i : Fin 200, Compatible (452600 + i.val) →
    (table.lookup (452600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2263 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 452600 452800 :=
  FiniteIntervals.of_fin 452600 200 complete_chunk2263

lemma complete_chunk2264 : ∀ i : Fin 200, Compatible (452800 + i.val) →
    (table.lookup (452800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2264 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 452800 453000 :=
  FiniteIntervals.of_fin 452800 200 complete_chunk2264

lemma complete_chunk2265 : ∀ i : Fin 200, Compatible (453000 + i.val) →
    (table.lookup (453000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2265 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 453000 453200 :=
  FiniteIntervals.of_fin 453000 200 complete_chunk2265

lemma complete_chunk2266 : ∀ i : Fin 200, Compatible (453200 + i.val) →
    (table.lookup (453200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2266 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 453200 453400 :=
  FiniteIntervals.of_fin 453200 200 complete_chunk2266

lemma complete_chunk2267 : ∀ i : Fin 200, Compatible (453400 + i.val) →
    (table.lookup (453400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2267 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 453400 453600 :=
  FiniteIntervals.of_fin 453400 200 complete_chunk2267

lemma complete_chunk2268 : ∀ i : Fin 200, Compatible (453600 + i.val) →
    (table.lookup (453600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2268 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 453600 453800 :=
  FiniteIntervals.of_fin 453600 200 complete_chunk2268

lemma complete_chunk2269 : ∀ i : Fin 200, Compatible (453800 + i.val) →
    (table.lookup (453800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2269 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 453800 454000 :=
  FiniteIntervals.of_fin 453800 200 complete_chunk2269

#print axioms interval_chunk2260
end Erdos184Work.PureFiveFilter4
