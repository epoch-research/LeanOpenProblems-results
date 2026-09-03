import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5270 : ∀ i : Fin 200, Compatible (1054000 + i.val) →
    (table.lookup (1054000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5270 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1054000 1054200 :=
  FiniteIntervals.of_fin 1054000 200 complete_chunk5270

lemma complete_chunk5271 : ∀ i : Fin 200, Compatible (1054200 + i.val) →
    (table.lookup (1054200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5271 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1054200 1054400 :=
  FiniteIntervals.of_fin 1054200 200 complete_chunk5271

lemma complete_chunk5272 : ∀ i : Fin 200, Compatible (1054400 + i.val) →
    (table.lookup (1054400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5272 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1054400 1054600 :=
  FiniteIntervals.of_fin 1054400 200 complete_chunk5272

lemma complete_chunk5273 : ∀ i : Fin 200, Compatible (1054600 + i.val) →
    (table.lookup (1054600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5273 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1054600 1054800 :=
  FiniteIntervals.of_fin 1054600 200 complete_chunk5273

lemma complete_chunk5274 : ∀ i : Fin 200, Compatible (1054800 + i.val) →
    (table.lookup (1054800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5274 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1054800 1055000 :=
  FiniteIntervals.of_fin 1054800 200 complete_chunk5274

lemma complete_chunk5275 : ∀ i : Fin 200, Compatible (1055000 + i.val) →
    (table.lookup (1055000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5275 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1055000 1055200 :=
  FiniteIntervals.of_fin 1055000 200 complete_chunk5275

lemma complete_chunk5276 : ∀ i : Fin 200, Compatible (1055200 + i.val) →
    (table.lookup (1055200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5276 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1055200 1055400 :=
  FiniteIntervals.of_fin 1055200 200 complete_chunk5276

lemma complete_chunk5277 : ∀ i : Fin 200, Compatible (1055400 + i.val) →
    (table.lookup (1055400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5277 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1055400 1055600 :=
  FiniteIntervals.of_fin 1055400 200 complete_chunk5277

lemma complete_chunk5278 : ∀ i : Fin 200, Compatible (1055600 + i.val) →
    (table.lookup (1055600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5278 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1055600 1055800 :=
  FiniteIntervals.of_fin 1055600 200 complete_chunk5278

lemma complete_chunk5279 : ∀ i : Fin 200, Compatible (1055800 + i.val) →
    (table.lookup (1055800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5279 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1055800 1056000 :=
  FiniteIntervals.of_fin 1055800 200 complete_chunk5279

#print axioms interval_chunk5270
end Erdos184Work.PureFiveFilter4
