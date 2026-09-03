import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2190 : ∀ i : Fin 200, Compatible (438000 + i.val) →
    (table.lookup (438000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2190 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 438000 438200 :=
  FiniteIntervals.of_fin 438000 200 complete_chunk2190

lemma complete_chunk2191 : ∀ i : Fin 200, Compatible (438200 + i.val) →
    (table.lookup (438200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2191 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 438200 438400 :=
  FiniteIntervals.of_fin 438200 200 complete_chunk2191

lemma complete_chunk2192 : ∀ i : Fin 200, Compatible (438400 + i.val) →
    (table.lookup (438400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2192 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 438400 438600 :=
  FiniteIntervals.of_fin 438400 200 complete_chunk2192

lemma complete_chunk2193 : ∀ i : Fin 200, Compatible (438600 + i.val) →
    (table.lookup (438600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2193 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 438600 438800 :=
  FiniteIntervals.of_fin 438600 200 complete_chunk2193

lemma complete_chunk2194 : ∀ i : Fin 200, Compatible (438800 + i.val) →
    (table.lookup (438800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2194 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 438800 439000 :=
  FiniteIntervals.of_fin 438800 200 complete_chunk2194

lemma complete_chunk2195 : ∀ i : Fin 200, Compatible (439000 + i.val) →
    (table.lookup (439000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2195 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 439000 439200 :=
  FiniteIntervals.of_fin 439000 200 complete_chunk2195

lemma complete_chunk2196 : ∀ i : Fin 200, Compatible (439200 + i.val) →
    (table.lookup (439200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2196 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 439200 439400 :=
  FiniteIntervals.of_fin 439200 200 complete_chunk2196

lemma complete_chunk2197 : ∀ i : Fin 200, Compatible (439400 + i.val) →
    (table.lookup (439400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2197 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 439400 439600 :=
  FiniteIntervals.of_fin 439400 200 complete_chunk2197

lemma complete_chunk2198 : ∀ i : Fin 200, Compatible (439600 + i.val) →
    (table.lookup (439600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2198 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 439600 439800 :=
  FiniteIntervals.of_fin 439600 200 complete_chunk2198

lemma complete_chunk2199 : ∀ i : Fin 200, Compatible (439800 + i.val) →
    (table.lookup (439800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2199 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 439800 440000 :=
  FiniteIntervals.of_fin 439800 200 complete_chunk2199

#print axioms interval_chunk2190
end Erdos184Work.PureFiveFilter4
