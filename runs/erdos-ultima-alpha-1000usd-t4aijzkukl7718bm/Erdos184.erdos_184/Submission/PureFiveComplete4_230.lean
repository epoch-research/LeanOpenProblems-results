import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2300 : ∀ i : Fin 200, Compatible (460000 + i.val) →
    (table.lookup (460000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2300 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 460000 460200 :=
  FiniteIntervals.of_fin 460000 200 complete_chunk2300

lemma complete_chunk2301 : ∀ i : Fin 200, Compatible (460200 + i.val) →
    (table.lookup (460200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2301 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 460200 460400 :=
  FiniteIntervals.of_fin 460200 200 complete_chunk2301

lemma complete_chunk2302 : ∀ i : Fin 200, Compatible (460400 + i.val) →
    (table.lookup (460400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2302 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 460400 460600 :=
  FiniteIntervals.of_fin 460400 200 complete_chunk2302

lemma complete_chunk2303 : ∀ i : Fin 200, Compatible (460600 + i.val) →
    (table.lookup (460600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2303 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 460600 460800 :=
  FiniteIntervals.of_fin 460600 200 complete_chunk2303

lemma complete_chunk2304 : ∀ i : Fin 200, Compatible (460800 + i.val) →
    (table.lookup (460800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2304 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 460800 461000 :=
  FiniteIntervals.of_fin 460800 200 complete_chunk2304

lemma complete_chunk2305 : ∀ i : Fin 200, Compatible (461000 + i.val) →
    (table.lookup (461000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2305 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 461000 461200 :=
  FiniteIntervals.of_fin 461000 200 complete_chunk2305

lemma complete_chunk2306 : ∀ i : Fin 200, Compatible (461200 + i.val) →
    (table.lookup (461200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2306 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 461200 461400 :=
  FiniteIntervals.of_fin 461200 200 complete_chunk2306

lemma complete_chunk2307 : ∀ i : Fin 200, Compatible (461400 + i.val) →
    (table.lookup (461400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2307 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 461400 461600 :=
  FiniteIntervals.of_fin 461400 200 complete_chunk2307

lemma complete_chunk2308 : ∀ i : Fin 200, Compatible (461600 + i.val) →
    (table.lookup (461600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2308 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 461600 461800 :=
  FiniteIntervals.of_fin 461600 200 complete_chunk2308

lemma complete_chunk2309 : ∀ i : Fin 200, Compatible (461800 + i.val) →
    (table.lookup (461800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2309 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 461800 462000 :=
  FiniteIntervals.of_fin 461800 200 complete_chunk2309

#print axioms interval_chunk2300
end Erdos184Work.PureFiveFilter4
