import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3310 : ∀ i : Fin 200, Compatible (662000 + i.val) →
    (table.lookup (662000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3310 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 662000 662200 :=
  FiniteIntervals.of_fin 662000 200 complete_chunk3310

lemma complete_chunk3311 : ∀ i : Fin 200, Compatible (662200 + i.val) →
    (table.lookup (662200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3311 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 662200 662400 :=
  FiniteIntervals.of_fin 662200 200 complete_chunk3311

lemma complete_chunk3312 : ∀ i : Fin 200, Compatible (662400 + i.val) →
    (table.lookup (662400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3312 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 662400 662600 :=
  FiniteIntervals.of_fin 662400 200 complete_chunk3312

lemma complete_chunk3313 : ∀ i : Fin 200, Compatible (662600 + i.val) →
    (table.lookup (662600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3313 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 662600 662800 :=
  FiniteIntervals.of_fin 662600 200 complete_chunk3313

lemma complete_chunk3314 : ∀ i : Fin 200, Compatible (662800 + i.val) →
    (table.lookup (662800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3314 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 662800 663000 :=
  FiniteIntervals.of_fin 662800 200 complete_chunk3314

lemma complete_chunk3315 : ∀ i : Fin 200, Compatible (663000 + i.val) →
    (table.lookup (663000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3315 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 663000 663200 :=
  FiniteIntervals.of_fin 663000 200 complete_chunk3315

lemma complete_chunk3316 : ∀ i : Fin 200, Compatible (663200 + i.val) →
    (table.lookup (663200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3316 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 663200 663400 :=
  FiniteIntervals.of_fin 663200 200 complete_chunk3316

lemma complete_chunk3317 : ∀ i : Fin 200, Compatible (663400 + i.val) →
    (table.lookup (663400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3317 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 663400 663600 :=
  FiniteIntervals.of_fin 663400 200 complete_chunk3317

lemma complete_chunk3318 : ∀ i : Fin 200, Compatible (663600 + i.val) →
    (table.lookup (663600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3318 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 663600 663800 :=
  FiniteIntervals.of_fin 663600 200 complete_chunk3318

lemma complete_chunk3319 : ∀ i : Fin 200, Compatible (663800 + i.val) →
    (table.lookup (663800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3319 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 663800 664000 :=
  FiniteIntervals.of_fin 663800 200 complete_chunk3319

#print axioms interval_chunk3310
end Erdos184Work.PureFiveFilter4
