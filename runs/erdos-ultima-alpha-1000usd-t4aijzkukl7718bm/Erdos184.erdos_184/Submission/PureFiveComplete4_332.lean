import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3320 : ∀ i : Fin 200, Compatible (664000 + i.val) →
    (table.lookup (664000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3320 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 664000 664200 :=
  FiniteIntervals.of_fin 664000 200 complete_chunk3320

lemma complete_chunk3321 : ∀ i : Fin 200, Compatible (664200 + i.val) →
    (table.lookup (664200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3321 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 664200 664400 :=
  FiniteIntervals.of_fin 664200 200 complete_chunk3321

lemma complete_chunk3322 : ∀ i : Fin 200, Compatible (664400 + i.val) →
    (table.lookup (664400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3322 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 664400 664600 :=
  FiniteIntervals.of_fin 664400 200 complete_chunk3322

lemma complete_chunk3323 : ∀ i : Fin 200, Compatible (664600 + i.val) →
    (table.lookup (664600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3323 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 664600 664800 :=
  FiniteIntervals.of_fin 664600 200 complete_chunk3323

lemma complete_chunk3324 : ∀ i : Fin 200, Compatible (664800 + i.val) →
    (table.lookup (664800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3324 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 664800 665000 :=
  FiniteIntervals.of_fin 664800 200 complete_chunk3324

lemma complete_chunk3325 : ∀ i : Fin 200, Compatible (665000 + i.val) →
    (table.lookup (665000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3325 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 665000 665200 :=
  FiniteIntervals.of_fin 665000 200 complete_chunk3325

lemma complete_chunk3326 : ∀ i : Fin 200, Compatible (665200 + i.val) →
    (table.lookup (665200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3326 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 665200 665400 :=
  FiniteIntervals.of_fin 665200 200 complete_chunk3326

lemma complete_chunk3327 : ∀ i : Fin 200, Compatible (665400 + i.val) →
    (table.lookup (665400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3327 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 665400 665600 :=
  FiniteIntervals.of_fin 665400 200 complete_chunk3327

lemma complete_chunk3328 : ∀ i : Fin 200, Compatible (665600 + i.val) →
    (table.lookup (665600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3328 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 665600 665800 :=
  FiniteIntervals.of_fin 665600 200 complete_chunk3328

lemma complete_chunk3329 : ∀ i : Fin 200, Compatible (665800 + i.val) →
    (table.lookup (665800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3329 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 665800 666000 :=
  FiniteIntervals.of_fin 665800 200 complete_chunk3329

#print axioms interval_chunk3320
end Erdos184Work.PureFiveFilter4
