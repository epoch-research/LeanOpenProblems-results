import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2250 : ∀ i : Fin 200, Compatible (450000 + i.val) →
    (table.lookup (450000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2250 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 450000 450200 :=
  FiniteIntervals.of_fin 450000 200 complete_chunk2250

lemma complete_chunk2251 : ∀ i : Fin 200, Compatible (450200 + i.val) →
    (table.lookup (450200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2251 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 450200 450400 :=
  FiniteIntervals.of_fin 450200 200 complete_chunk2251

lemma complete_chunk2252 : ∀ i : Fin 200, Compatible (450400 + i.val) →
    (table.lookup (450400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2252 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 450400 450600 :=
  FiniteIntervals.of_fin 450400 200 complete_chunk2252

lemma complete_chunk2253 : ∀ i : Fin 200, Compatible (450600 + i.val) →
    (table.lookup (450600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2253 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 450600 450800 :=
  FiniteIntervals.of_fin 450600 200 complete_chunk2253

lemma complete_chunk2254 : ∀ i : Fin 200, Compatible (450800 + i.val) →
    (table.lookup (450800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2254 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 450800 451000 :=
  FiniteIntervals.of_fin 450800 200 complete_chunk2254

lemma complete_chunk2255 : ∀ i : Fin 200, Compatible (451000 + i.val) →
    (table.lookup (451000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2255 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 451000 451200 :=
  FiniteIntervals.of_fin 451000 200 complete_chunk2255

lemma complete_chunk2256 : ∀ i : Fin 200, Compatible (451200 + i.val) →
    (table.lookup (451200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2256 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 451200 451400 :=
  FiniteIntervals.of_fin 451200 200 complete_chunk2256

lemma complete_chunk2257 : ∀ i : Fin 200, Compatible (451400 + i.val) →
    (table.lookup (451400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2257 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 451400 451600 :=
  FiniteIntervals.of_fin 451400 200 complete_chunk2257

lemma complete_chunk2258 : ∀ i : Fin 200, Compatible (451600 + i.val) →
    (table.lookup (451600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2258 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 451600 451800 :=
  FiniteIntervals.of_fin 451600 200 complete_chunk2258

lemma complete_chunk2259 : ∀ i : Fin 200, Compatible (451800 + i.val) →
    (table.lookup (451800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2259 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 451800 452000 :=
  FiniteIntervals.of_fin 451800 200 complete_chunk2259

#print axioms interval_chunk2250
end Erdos184Work.PureFiveFilter4
