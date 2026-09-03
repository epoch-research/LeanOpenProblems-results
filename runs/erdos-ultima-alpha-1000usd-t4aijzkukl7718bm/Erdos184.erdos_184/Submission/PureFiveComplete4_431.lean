import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4310 : ∀ i : Fin 200, Compatible (862000 + i.val) →
    (table.lookup (862000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4310 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 862000 862200 :=
  FiniteIntervals.of_fin 862000 200 complete_chunk4310

lemma complete_chunk4311 : ∀ i : Fin 200, Compatible (862200 + i.val) →
    (table.lookup (862200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4311 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 862200 862400 :=
  FiniteIntervals.of_fin 862200 200 complete_chunk4311

lemma complete_chunk4312 : ∀ i : Fin 200, Compatible (862400 + i.val) →
    (table.lookup (862400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4312 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 862400 862600 :=
  FiniteIntervals.of_fin 862400 200 complete_chunk4312

lemma complete_chunk4313 : ∀ i : Fin 200, Compatible (862600 + i.val) →
    (table.lookup (862600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4313 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 862600 862800 :=
  FiniteIntervals.of_fin 862600 200 complete_chunk4313

lemma complete_chunk4314 : ∀ i : Fin 200, Compatible (862800 + i.val) →
    (table.lookup (862800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4314 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 862800 863000 :=
  FiniteIntervals.of_fin 862800 200 complete_chunk4314

lemma complete_chunk4315 : ∀ i : Fin 200, Compatible (863000 + i.val) →
    (table.lookup (863000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4315 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 863000 863200 :=
  FiniteIntervals.of_fin 863000 200 complete_chunk4315

lemma complete_chunk4316 : ∀ i : Fin 200, Compatible (863200 + i.val) →
    (table.lookup (863200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4316 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 863200 863400 :=
  FiniteIntervals.of_fin 863200 200 complete_chunk4316

lemma complete_chunk4317 : ∀ i : Fin 200, Compatible (863400 + i.val) →
    (table.lookup (863400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4317 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 863400 863600 :=
  FiniteIntervals.of_fin 863400 200 complete_chunk4317

lemma complete_chunk4318 : ∀ i : Fin 200, Compatible (863600 + i.val) →
    (table.lookup (863600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4318 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 863600 863800 :=
  FiniteIntervals.of_fin 863600 200 complete_chunk4318

lemma complete_chunk4319 : ∀ i : Fin 200, Compatible (863800 + i.val) →
    (table.lookup (863800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4319 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 863800 864000 :=
  FiniteIntervals.of_fin 863800 200 complete_chunk4319

#print axioms interval_chunk4310
end Erdos184Work.PureFiveFilter4
