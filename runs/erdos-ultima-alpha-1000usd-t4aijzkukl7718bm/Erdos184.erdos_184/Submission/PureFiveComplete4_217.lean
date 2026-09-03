import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2170 : ∀ i : Fin 200, Compatible (434000 + i.val) →
    (table.lookup (434000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2170 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 434000 434200 :=
  FiniteIntervals.of_fin 434000 200 complete_chunk2170

lemma complete_chunk2171 : ∀ i : Fin 200, Compatible (434200 + i.val) →
    (table.lookup (434200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2171 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 434200 434400 :=
  FiniteIntervals.of_fin 434200 200 complete_chunk2171

lemma complete_chunk2172 : ∀ i : Fin 200, Compatible (434400 + i.val) →
    (table.lookup (434400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2172 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 434400 434600 :=
  FiniteIntervals.of_fin 434400 200 complete_chunk2172

lemma complete_chunk2173 : ∀ i : Fin 200, Compatible (434600 + i.val) →
    (table.lookup (434600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2173 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 434600 434800 :=
  FiniteIntervals.of_fin 434600 200 complete_chunk2173

lemma complete_chunk2174 : ∀ i : Fin 200, Compatible (434800 + i.val) →
    (table.lookup (434800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2174 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 434800 435000 :=
  FiniteIntervals.of_fin 434800 200 complete_chunk2174

lemma complete_chunk2175 : ∀ i : Fin 200, Compatible (435000 + i.val) →
    (table.lookup (435000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2175 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 435000 435200 :=
  FiniteIntervals.of_fin 435000 200 complete_chunk2175

lemma complete_chunk2176 : ∀ i : Fin 200, Compatible (435200 + i.val) →
    (table.lookup (435200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2176 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 435200 435400 :=
  FiniteIntervals.of_fin 435200 200 complete_chunk2176

lemma complete_chunk2177 : ∀ i : Fin 200, Compatible (435400 + i.val) →
    (table.lookup (435400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2177 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 435400 435600 :=
  FiniteIntervals.of_fin 435400 200 complete_chunk2177

lemma complete_chunk2178 : ∀ i : Fin 200, Compatible (435600 + i.val) →
    (table.lookup (435600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2178 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 435600 435800 :=
  FiniteIntervals.of_fin 435600 200 complete_chunk2178

lemma complete_chunk2179 : ∀ i : Fin 200, Compatible (435800 + i.val) →
    (table.lookup (435800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2179 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 435800 436000 :=
  FiniteIntervals.of_fin 435800 200 complete_chunk2179

#print axioms interval_chunk2170
end Erdos184Work.PureFiveFilter4
