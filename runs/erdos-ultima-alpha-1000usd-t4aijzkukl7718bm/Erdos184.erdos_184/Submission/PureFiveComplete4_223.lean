import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2230 : ∀ i : Fin 200, Compatible (446000 + i.val) →
    (table.lookup (446000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2230 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 446000 446200 :=
  FiniteIntervals.of_fin 446000 200 complete_chunk2230

lemma complete_chunk2231 : ∀ i : Fin 200, Compatible (446200 + i.val) →
    (table.lookup (446200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2231 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 446200 446400 :=
  FiniteIntervals.of_fin 446200 200 complete_chunk2231

lemma complete_chunk2232 : ∀ i : Fin 200, Compatible (446400 + i.val) →
    (table.lookup (446400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2232 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 446400 446600 :=
  FiniteIntervals.of_fin 446400 200 complete_chunk2232

lemma complete_chunk2233 : ∀ i : Fin 200, Compatible (446600 + i.val) →
    (table.lookup (446600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2233 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 446600 446800 :=
  FiniteIntervals.of_fin 446600 200 complete_chunk2233

lemma complete_chunk2234 : ∀ i : Fin 200, Compatible (446800 + i.val) →
    (table.lookup (446800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2234 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 446800 447000 :=
  FiniteIntervals.of_fin 446800 200 complete_chunk2234

lemma complete_chunk2235 : ∀ i : Fin 200, Compatible (447000 + i.val) →
    (table.lookup (447000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2235 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 447000 447200 :=
  FiniteIntervals.of_fin 447000 200 complete_chunk2235

lemma complete_chunk2236 : ∀ i : Fin 200, Compatible (447200 + i.val) →
    (table.lookup (447200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2236 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 447200 447400 :=
  FiniteIntervals.of_fin 447200 200 complete_chunk2236

lemma complete_chunk2237 : ∀ i : Fin 200, Compatible (447400 + i.val) →
    (table.lookup (447400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2237 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 447400 447600 :=
  FiniteIntervals.of_fin 447400 200 complete_chunk2237

lemma complete_chunk2238 : ∀ i : Fin 200, Compatible (447600 + i.val) →
    (table.lookup (447600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2238 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 447600 447800 :=
  FiniteIntervals.of_fin 447600 200 complete_chunk2238

lemma complete_chunk2239 : ∀ i : Fin 200, Compatible (447800 + i.val) →
    (table.lookup (447800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2239 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 447800 448000 :=
  FiniteIntervals.of_fin 447800 200 complete_chunk2239

#print axioms interval_chunk2230
end Erdos184Work.PureFiveFilter4
