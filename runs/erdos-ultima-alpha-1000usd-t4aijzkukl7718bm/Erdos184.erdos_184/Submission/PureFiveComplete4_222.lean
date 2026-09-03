import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2220 : ∀ i : Fin 200, Compatible (444000 + i.val) →
    (table.lookup (444000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2220 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 444000 444200 :=
  FiniteIntervals.of_fin 444000 200 complete_chunk2220

lemma complete_chunk2221 : ∀ i : Fin 200, Compatible (444200 + i.val) →
    (table.lookup (444200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2221 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 444200 444400 :=
  FiniteIntervals.of_fin 444200 200 complete_chunk2221

lemma complete_chunk2222 : ∀ i : Fin 200, Compatible (444400 + i.val) →
    (table.lookup (444400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2222 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 444400 444600 :=
  FiniteIntervals.of_fin 444400 200 complete_chunk2222

lemma complete_chunk2223 : ∀ i : Fin 200, Compatible (444600 + i.val) →
    (table.lookup (444600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2223 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 444600 444800 :=
  FiniteIntervals.of_fin 444600 200 complete_chunk2223

lemma complete_chunk2224 : ∀ i : Fin 200, Compatible (444800 + i.val) →
    (table.lookup (444800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2224 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 444800 445000 :=
  FiniteIntervals.of_fin 444800 200 complete_chunk2224

lemma complete_chunk2225 : ∀ i : Fin 200, Compatible (445000 + i.val) →
    (table.lookup (445000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2225 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 445000 445200 :=
  FiniteIntervals.of_fin 445000 200 complete_chunk2225

lemma complete_chunk2226 : ∀ i : Fin 200, Compatible (445200 + i.val) →
    (table.lookup (445200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2226 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 445200 445400 :=
  FiniteIntervals.of_fin 445200 200 complete_chunk2226

lemma complete_chunk2227 : ∀ i : Fin 200, Compatible (445400 + i.val) →
    (table.lookup (445400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2227 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 445400 445600 :=
  FiniteIntervals.of_fin 445400 200 complete_chunk2227

lemma complete_chunk2228 : ∀ i : Fin 200, Compatible (445600 + i.val) →
    (table.lookup (445600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2228 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 445600 445800 :=
  FiniteIntervals.of_fin 445600 200 complete_chunk2228

lemma complete_chunk2229 : ∀ i : Fin 200, Compatible (445800 + i.val) →
    (table.lookup (445800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2229 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 445800 446000 :=
  FiniteIntervals.of_fin 445800 200 complete_chunk2229

#print axioms interval_chunk2220
end Erdos184Work.PureFiveFilter4
