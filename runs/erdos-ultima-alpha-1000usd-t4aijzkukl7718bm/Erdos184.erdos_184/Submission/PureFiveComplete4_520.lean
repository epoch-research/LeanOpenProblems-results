import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5200 : ∀ i : Fin 200, Compatible (1040000 + i.val) →
    (table.lookup (1040000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5200 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1040000 1040200 :=
  FiniteIntervals.of_fin 1040000 200 complete_chunk5200

lemma complete_chunk5201 : ∀ i : Fin 200, Compatible (1040200 + i.val) →
    (table.lookup (1040200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5201 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1040200 1040400 :=
  FiniteIntervals.of_fin 1040200 200 complete_chunk5201

lemma complete_chunk5202 : ∀ i : Fin 200, Compatible (1040400 + i.val) →
    (table.lookup (1040400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5202 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1040400 1040600 :=
  FiniteIntervals.of_fin 1040400 200 complete_chunk5202

lemma complete_chunk5203 : ∀ i : Fin 200, Compatible (1040600 + i.val) →
    (table.lookup (1040600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5203 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1040600 1040800 :=
  FiniteIntervals.of_fin 1040600 200 complete_chunk5203

lemma complete_chunk5204 : ∀ i : Fin 200, Compatible (1040800 + i.val) →
    (table.lookup (1040800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5204 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1040800 1041000 :=
  FiniteIntervals.of_fin 1040800 200 complete_chunk5204

lemma complete_chunk5205 : ∀ i : Fin 200, Compatible (1041000 + i.val) →
    (table.lookup (1041000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5205 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1041000 1041200 :=
  FiniteIntervals.of_fin 1041000 200 complete_chunk5205

lemma complete_chunk5206 : ∀ i : Fin 200, Compatible (1041200 + i.val) →
    (table.lookup (1041200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5206 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1041200 1041400 :=
  FiniteIntervals.of_fin 1041200 200 complete_chunk5206

lemma complete_chunk5207 : ∀ i : Fin 200, Compatible (1041400 + i.val) →
    (table.lookup (1041400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5207 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1041400 1041600 :=
  FiniteIntervals.of_fin 1041400 200 complete_chunk5207

lemma complete_chunk5208 : ∀ i : Fin 200, Compatible (1041600 + i.val) →
    (table.lookup (1041600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5208 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1041600 1041800 :=
  FiniteIntervals.of_fin 1041600 200 complete_chunk5208

lemma complete_chunk5209 : ∀ i : Fin 200, Compatible (1041800 + i.val) →
    (table.lookup (1041800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5209 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1041800 1042000 :=
  FiniteIntervals.of_fin 1041800 200 complete_chunk5209

#print axioms interval_chunk5200
end Erdos184Work.PureFiveFilter4
