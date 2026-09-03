import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1260 : ∀ i : Fin 200, Compatible (252000 + i.val) →
    (table.lookup (252000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1260 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 252000 252200 :=
  FiniteIntervals.of_fin 252000 200 complete_chunk1260

lemma complete_chunk1261 : ∀ i : Fin 200, Compatible (252200 + i.val) →
    (table.lookup (252200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1261 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 252200 252400 :=
  FiniteIntervals.of_fin 252200 200 complete_chunk1261

lemma complete_chunk1262 : ∀ i : Fin 200, Compatible (252400 + i.val) →
    (table.lookup (252400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1262 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 252400 252600 :=
  FiniteIntervals.of_fin 252400 200 complete_chunk1262

lemma complete_chunk1263 : ∀ i : Fin 200, Compatible (252600 + i.val) →
    (table.lookup (252600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1263 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 252600 252800 :=
  FiniteIntervals.of_fin 252600 200 complete_chunk1263

lemma complete_chunk1264 : ∀ i : Fin 200, Compatible (252800 + i.val) →
    (table.lookup (252800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1264 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 252800 253000 :=
  FiniteIntervals.of_fin 252800 200 complete_chunk1264

lemma complete_chunk1265 : ∀ i : Fin 200, Compatible (253000 + i.val) →
    (table.lookup (253000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1265 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 253000 253200 :=
  FiniteIntervals.of_fin 253000 200 complete_chunk1265

lemma complete_chunk1266 : ∀ i : Fin 200, Compatible (253200 + i.val) →
    (table.lookup (253200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1266 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 253200 253400 :=
  FiniteIntervals.of_fin 253200 200 complete_chunk1266

lemma complete_chunk1267 : ∀ i : Fin 200, Compatible (253400 + i.val) →
    (table.lookup (253400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1267 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 253400 253600 :=
  FiniteIntervals.of_fin 253400 200 complete_chunk1267

lemma complete_chunk1268 : ∀ i : Fin 200, Compatible (253600 + i.val) →
    (table.lookup (253600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1268 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 253600 253800 :=
  FiniteIntervals.of_fin 253600 200 complete_chunk1268

lemma complete_chunk1269 : ∀ i : Fin 200, Compatible (253800 + i.val) →
    (table.lookup (253800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1269 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 253800 254000 :=
  FiniteIntervals.of_fin 253800 200 complete_chunk1269

#print axioms interval_chunk1260
end Erdos184Work.PureFiveFilter4
