import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1280 : ∀ i : Fin 200, Compatible (256000 + i.val) →
    (table.lookup (256000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1280 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 256000 256200 :=
  FiniteIntervals.of_fin 256000 200 complete_chunk1280

lemma complete_chunk1281 : ∀ i : Fin 200, Compatible (256200 + i.val) →
    (table.lookup (256200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1281 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 256200 256400 :=
  FiniteIntervals.of_fin 256200 200 complete_chunk1281

lemma complete_chunk1282 : ∀ i : Fin 200, Compatible (256400 + i.val) →
    (table.lookup (256400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1282 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 256400 256600 :=
  FiniteIntervals.of_fin 256400 200 complete_chunk1282

lemma complete_chunk1283 : ∀ i : Fin 200, Compatible (256600 + i.val) →
    (table.lookup (256600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1283 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 256600 256800 :=
  FiniteIntervals.of_fin 256600 200 complete_chunk1283

lemma complete_chunk1284 : ∀ i : Fin 200, Compatible (256800 + i.val) →
    (table.lookup (256800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1284 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 256800 257000 :=
  FiniteIntervals.of_fin 256800 200 complete_chunk1284

lemma complete_chunk1285 : ∀ i : Fin 200, Compatible (257000 + i.val) →
    (table.lookup (257000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1285 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 257000 257200 :=
  FiniteIntervals.of_fin 257000 200 complete_chunk1285

lemma complete_chunk1286 : ∀ i : Fin 200, Compatible (257200 + i.val) →
    (table.lookup (257200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1286 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 257200 257400 :=
  FiniteIntervals.of_fin 257200 200 complete_chunk1286

lemma complete_chunk1287 : ∀ i : Fin 200, Compatible (257400 + i.val) →
    (table.lookup (257400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1287 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 257400 257600 :=
  FiniteIntervals.of_fin 257400 200 complete_chunk1287

lemma complete_chunk1288 : ∀ i : Fin 200, Compatible (257600 + i.val) →
    (table.lookup (257600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1288 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 257600 257800 :=
  FiniteIntervals.of_fin 257600 200 complete_chunk1288

lemma complete_chunk1289 : ∀ i : Fin 200, Compatible (257800 + i.val) →
    (table.lookup (257800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1289 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 257800 258000 :=
  FiniteIntervals.of_fin 257800 200 complete_chunk1289

#print axioms interval_chunk1280
end Erdos184Work.PureFiveFilter4
