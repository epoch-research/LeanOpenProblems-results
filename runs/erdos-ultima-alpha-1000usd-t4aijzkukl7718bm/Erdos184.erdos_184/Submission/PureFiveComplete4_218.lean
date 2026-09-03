import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2180 : ∀ i : Fin 200, Compatible (436000 + i.val) →
    (table.lookup (436000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2180 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 436000 436200 :=
  FiniteIntervals.of_fin 436000 200 complete_chunk2180

lemma complete_chunk2181 : ∀ i : Fin 200, Compatible (436200 + i.val) →
    (table.lookup (436200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2181 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 436200 436400 :=
  FiniteIntervals.of_fin 436200 200 complete_chunk2181

lemma complete_chunk2182 : ∀ i : Fin 200, Compatible (436400 + i.val) →
    (table.lookup (436400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2182 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 436400 436600 :=
  FiniteIntervals.of_fin 436400 200 complete_chunk2182

lemma complete_chunk2183 : ∀ i : Fin 200, Compatible (436600 + i.val) →
    (table.lookup (436600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2183 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 436600 436800 :=
  FiniteIntervals.of_fin 436600 200 complete_chunk2183

lemma complete_chunk2184 : ∀ i : Fin 200, Compatible (436800 + i.val) →
    (table.lookup (436800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2184 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 436800 437000 :=
  FiniteIntervals.of_fin 436800 200 complete_chunk2184

lemma complete_chunk2185 : ∀ i : Fin 200, Compatible (437000 + i.val) →
    (table.lookup (437000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2185 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 437000 437200 :=
  FiniteIntervals.of_fin 437000 200 complete_chunk2185

lemma complete_chunk2186 : ∀ i : Fin 200, Compatible (437200 + i.val) →
    (table.lookup (437200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2186 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 437200 437400 :=
  FiniteIntervals.of_fin 437200 200 complete_chunk2186

lemma complete_chunk2187 : ∀ i : Fin 200, Compatible (437400 + i.val) →
    (table.lookup (437400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2187 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 437400 437600 :=
  FiniteIntervals.of_fin 437400 200 complete_chunk2187

lemma complete_chunk2188 : ∀ i : Fin 200, Compatible (437600 + i.val) →
    (table.lookup (437600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2188 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 437600 437800 :=
  FiniteIntervals.of_fin 437600 200 complete_chunk2188

lemma complete_chunk2189 : ∀ i : Fin 200, Compatible (437800 + i.val) →
    (table.lookup (437800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2189 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 437800 438000 :=
  FiniteIntervals.of_fin 437800 200 complete_chunk2189

#print axioms interval_chunk2180
end Erdos184Work.PureFiveFilter4
