import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3220 : ∀ i : Fin 200, Compatible (644000 + i.val) →
    (table.lookup (644000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3220 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 644000 644200 :=
  FiniteIntervals.of_fin 644000 200 complete_chunk3220

lemma complete_chunk3221 : ∀ i : Fin 200, Compatible (644200 + i.val) →
    (table.lookup (644200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3221 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 644200 644400 :=
  FiniteIntervals.of_fin 644200 200 complete_chunk3221

lemma complete_chunk3222 : ∀ i : Fin 200, Compatible (644400 + i.val) →
    (table.lookup (644400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3222 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 644400 644600 :=
  FiniteIntervals.of_fin 644400 200 complete_chunk3222

lemma complete_chunk3223 : ∀ i : Fin 200, Compatible (644600 + i.val) →
    (table.lookup (644600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3223 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 644600 644800 :=
  FiniteIntervals.of_fin 644600 200 complete_chunk3223

lemma complete_chunk3224 : ∀ i : Fin 200, Compatible (644800 + i.val) →
    (table.lookup (644800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3224 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 644800 645000 :=
  FiniteIntervals.of_fin 644800 200 complete_chunk3224

lemma complete_chunk3225 : ∀ i : Fin 200, Compatible (645000 + i.val) →
    (table.lookup (645000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3225 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 645000 645200 :=
  FiniteIntervals.of_fin 645000 200 complete_chunk3225

lemma complete_chunk3226 : ∀ i : Fin 200, Compatible (645200 + i.val) →
    (table.lookup (645200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3226 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 645200 645400 :=
  FiniteIntervals.of_fin 645200 200 complete_chunk3226

lemma complete_chunk3227 : ∀ i : Fin 200, Compatible (645400 + i.val) →
    (table.lookup (645400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3227 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 645400 645600 :=
  FiniteIntervals.of_fin 645400 200 complete_chunk3227

lemma complete_chunk3228 : ∀ i : Fin 200, Compatible (645600 + i.val) →
    (table.lookup (645600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3228 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 645600 645800 :=
  FiniteIntervals.of_fin 645600 200 complete_chunk3228

lemma complete_chunk3229 : ∀ i : Fin 200, Compatible (645800 + i.val) →
    (table.lookup (645800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3229 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 645800 646000 :=
  FiniteIntervals.of_fin 645800 200 complete_chunk3229

#print axioms interval_chunk3220
end Erdos184Work.PureFiveFilter4
