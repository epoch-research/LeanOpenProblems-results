import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1310 : ∀ i : Fin 200, Compatible (262000 + i.val) →
    (table.lookup (262000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1310 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 262000 262200 :=
  FiniteIntervals.of_fin 262000 200 complete_chunk1310

lemma complete_chunk1311 : ∀ i : Fin 200, Compatible (262200 + i.val) →
    (table.lookup (262200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1311 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 262200 262400 :=
  FiniteIntervals.of_fin 262200 200 complete_chunk1311

lemma complete_chunk1312 : ∀ i : Fin 200, Compatible (262400 + i.val) →
    (table.lookup (262400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1312 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 262400 262600 :=
  FiniteIntervals.of_fin 262400 200 complete_chunk1312

lemma complete_chunk1313 : ∀ i : Fin 200, Compatible (262600 + i.val) →
    (table.lookup (262600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1313 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 262600 262800 :=
  FiniteIntervals.of_fin 262600 200 complete_chunk1313

lemma complete_chunk1314 : ∀ i : Fin 200, Compatible (262800 + i.val) →
    (table.lookup (262800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1314 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 262800 263000 :=
  FiniteIntervals.of_fin 262800 200 complete_chunk1314

lemma complete_chunk1315 : ∀ i : Fin 200, Compatible (263000 + i.val) →
    (table.lookup (263000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1315 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 263000 263200 :=
  FiniteIntervals.of_fin 263000 200 complete_chunk1315

lemma complete_chunk1316 : ∀ i : Fin 200, Compatible (263200 + i.val) →
    (table.lookup (263200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1316 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 263200 263400 :=
  FiniteIntervals.of_fin 263200 200 complete_chunk1316

lemma complete_chunk1317 : ∀ i : Fin 200, Compatible (263400 + i.val) →
    (table.lookup (263400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1317 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 263400 263600 :=
  FiniteIntervals.of_fin 263400 200 complete_chunk1317

lemma complete_chunk1318 : ∀ i : Fin 200, Compatible (263600 + i.val) →
    (table.lookup (263600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1318 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 263600 263800 :=
  FiniteIntervals.of_fin 263600 200 complete_chunk1318

lemma complete_chunk1319 : ∀ i : Fin 200, Compatible (263800 + i.val) →
    (table.lookup (263800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1319 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 263800 264000 :=
  FiniteIntervals.of_fin 263800 200 complete_chunk1319

#print axioms interval_chunk1310
end Erdos184Work.PureFiveFilter4
