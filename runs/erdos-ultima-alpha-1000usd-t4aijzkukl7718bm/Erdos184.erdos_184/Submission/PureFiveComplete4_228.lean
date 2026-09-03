import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2280 : ∀ i : Fin 200, Compatible (456000 + i.val) →
    (table.lookup (456000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2280 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 456000 456200 :=
  FiniteIntervals.of_fin 456000 200 complete_chunk2280

lemma complete_chunk2281 : ∀ i : Fin 200, Compatible (456200 + i.val) →
    (table.lookup (456200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2281 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 456200 456400 :=
  FiniteIntervals.of_fin 456200 200 complete_chunk2281

lemma complete_chunk2282 : ∀ i : Fin 200, Compatible (456400 + i.val) →
    (table.lookup (456400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2282 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 456400 456600 :=
  FiniteIntervals.of_fin 456400 200 complete_chunk2282

lemma complete_chunk2283 : ∀ i : Fin 200, Compatible (456600 + i.val) →
    (table.lookup (456600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2283 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 456600 456800 :=
  FiniteIntervals.of_fin 456600 200 complete_chunk2283

lemma complete_chunk2284 : ∀ i : Fin 200, Compatible (456800 + i.val) →
    (table.lookup (456800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2284 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 456800 457000 :=
  FiniteIntervals.of_fin 456800 200 complete_chunk2284

lemma complete_chunk2285 : ∀ i : Fin 200, Compatible (457000 + i.val) →
    (table.lookup (457000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2285 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 457000 457200 :=
  FiniteIntervals.of_fin 457000 200 complete_chunk2285

lemma complete_chunk2286 : ∀ i : Fin 200, Compatible (457200 + i.val) →
    (table.lookup (457200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2286 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 457200 457400 :=
  FiniteIntervals.of_fin 457200 200 complete_chunk2286

lemma complete_chunk2287 : ∀ i : Fin 200, Compatible (457400 + i.val) →
    (table.lookup (457400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2287 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 457400 457600 :=
  FiniteIntervals.of_fin 457400 200 complete_chunk2287

lemma complete_chunk2288 : ∀ i : Fin 200, Compatible (457600 + i.val) →
    (table.lookup (457600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2288 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 457600 457800 :=
  FiniteIntervals.of_fin 457600 200 complete_chunk2288

lemma complete_chunk2289 : ∀ i : Fin 200, Compatible (457800 + i.val) →
    (table.lookup (457800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2289 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 457800 458000 :=
  FiniteIntervals.of_fin 457800 200 complete_chunk2289

#print axioms interval_chunk2280
end Erdos184Work.PureFiveFilter4
