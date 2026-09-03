import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2290 : ∀ i : Fin 200, Compatible (458000 + i.val) →
    (table.lookup (458000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2290 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 458000 458200 :=
  FiniteIntervals.of_fin 458000 200 complete_chunk2290

lemma complete_chunk2291 : ∀ i : Fin 200, Compatible (458200 + i.val) →
    (table.lookup (458200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2291 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 458200 458400 :=
  FiniteIntervals.of_fin 458200 200 complete_chunk2291

lemma complete_chunk2292 : ∀ i : Fin 200, Compatible (458400 + i.val) →
    (table.lookup (458400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2292 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 458400 458600 :=
  FiniteIntervals.of_fin 458400 200 complete_chunk2292

lemma complete_chunk2293 : ∀ i : Fin 200, Compatible (458600 + i.val) →
    (table.lookup (458600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2293 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 458600 458800 :=
  FiniteIntervals.of_fin 458600 200 complete_chunk2293

lemma complete_chunk2294 : ∀ i : Fin 200, Compatible (458800 + i.val) →
    (table.lookup (458800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2294 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 458800 459000 :=
  FiniteIntervals.of_fin 458800 200 complete_chunk2294

lemma complete_chunk2295 : ∀ i : Fin 200, Compatible (459000 + i.val) →
    (table.lookup (459000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2295 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 459000 459200 :=
  FiniteIntervals.of_fin 459000 200 complete_chunk2295

lemma complete_chunk2296 : ∀ i : Fin 200, Compatible (459200 + i.val) →
    (table.lookup (459200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2296 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 459200 459400 :=
  FiniteIntervals.of_fin 459200 200 complete_chunk2296

lemma complete_chunk2297 : ∀ i : Fin 200, Compatible (459400 + i.val) →
    (table.lookup (459400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2297 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 459400 459600 :=
  FiniteIntervals.of_fin 459400 200 complete_chunk2297

lemma complete_chunk2298 : ∀ i : Fin 200, Compatible (459600 + i.val) →
    (table.lookup (459600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2298 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 459600 459800 :=
  FiniteIntervals.of_fin 459600 200 complete_chunk2298

lemma complete_chunk2299 : ∀ i : Fin 200, Compatible (459800 + i.val) →
    (table.lookup (459800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2299 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 459800 460000 :=
  FiniteIntervals.of_fin 459800 200 complete_chunk2299

#print axioms interval_chunk2290
end Erdos184Work.PureFiveFilter4
