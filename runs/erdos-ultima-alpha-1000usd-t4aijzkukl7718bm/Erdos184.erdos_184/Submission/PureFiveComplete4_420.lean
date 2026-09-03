import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4200 : ∀ i : Fin 200, Compatible (840000 + i.val) →
    (table.lookup (840000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4200 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 840000 840200 :=
  FiniteIntervals.of_fin 840000 200 complete_chunk4200

lemma complete_chunk4201 : ∀ i : Fin 200, Compatible (840200 + i.val) →
    (table.lookup (840200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4201 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 840200 840400 :=
  FiniteIntervals.of_fin 840200 200 complete_chunk4201

lemma complete_chunk4202 : ∀ i : Fin 200, Compatible (840400 + i.val) →
    (table.lookup (840400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4202 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 840400 840600 :=
  FiniteIntervals.of_fin 840400 200 complete_chunk4202

lemma complete_chunk4203 : ∀ i : Fin 200, Compatible (840600 + i.val) →
    (table.lookup (840600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4203 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 840600 840800 :=
  FiniteIntervals.of_fin 840600 200 complete_chunk4203

lemma complete_chunk4204 : ∀ i : Fin 200, Compatible (840800 + i.val) →
    (table.lookup (840800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4204 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 840800 841000 :=
  FiniteIntervals.of_fin 840800 200 complete_chunk4204

lemma complete_chunk4205 : ∀ i : Fin 200, Compatible (841000 + i.val) →
    (table.lookup (841000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4205 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 841000 841200 :=
  FiniteIntervals.of_fin 841000 200 complete_chunk4205

lemma complete_chunk4206 : ∀ i : Fin 200, Compatible (841200 + i.val) →
    (table.lookup (841200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4206 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 841200 841400 :=
  FiniteIntervals.of_fin 841200 200 complete_chunk4206

lemma complete_chunk4207 : ∀ i : Fin 200, Compatible (841400 + i.val) →
    (table.lookup (841400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4207 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 841400 841600 :=
  FiniteIntervals.of_fin 841400 200 complete_chunk4207

lemma complete_chunk4208 : ∀ i : Fin 200, Compatible (841600 + i.val) →
    (table.lookup (841600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4208 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 841600 841800 :=
  FiniteIntervals.of_fin 841600 200 complete_chunk4208

lemma complete_chunk4209 : ∀ i : Fin 200, Compatible (841800 + i.val) →
    (table.lookup (841800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4209 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 841800 842000 :=
  FiniteIntervals.of_fin 841800 200 complete_chunk4209

#print axioms interval_chunk4200
end Erdos184Work.PureFiveFilter4
