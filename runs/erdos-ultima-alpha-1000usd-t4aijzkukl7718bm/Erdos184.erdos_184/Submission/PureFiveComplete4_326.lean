import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3260 : ∀ i : Fin 200, Compatible (652000 + i.val) →
    (table.lookup (652000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3260 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 652000 652200 :=
  FiniteIntervals.of_fin 652000 200 complete_chunk3260

lemma complete_chunk3261 : ∀ i : Fin 200, Compatible (652200 + i.val) →
    (table.lookup (652200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3261 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 652200 652400 :=
  FiniteIntervals.of_fin 652200 200 complete_chunk3261

lemma complete_chunk3262 : ∀ i : Fin 200, Compatible (652400 + i.val) →
    (table.lookup (652400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3262 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 652400 652600 :=
  FiniteIntervals.of_fin 652400 200 complete_chunk3262

lemma complete_chunk3263 : ∀ i : Fin 200, Compatible (652600 + i.val) →
    (table.lookup (652600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3263 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 652600 652800 :=
  FiniteIntervals.of_fin 652600 200 complete_chunk3263

lemma complete_chunk3264 : ∀ i : Fin 200, Compatible (652800 + i.val) →
    (table.lookup (652800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3264 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 652800 653000 :=
  FiniteIntervals.of_fin 652800 200 complete_chunk3264

lemma complete_chunk3265 : ∀ i : Fin 200, Compatible (653000 + i.val) →
    (table.lookup (653000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3265 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 653000 653200 :=
  FiniteIntervals.of_fin 653000 200 complete_chunk3265

lemma complete_chunk3266 : ∀ i : Fin 200, Compatible (653200 + i.val) →
    (table.lookup (653200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3266 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 653200 653400 :=
  FiniteIntervals.of_fin 653200 200 complete_chunk3266

lemma complete_chunk3267 : ∀ i : Fin 200, Compatible (653400 + i.val) →
    (table.lookup (653400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3267 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 653400 653600 :=
  FiniteIntervals.of_fin 653400 200 complete_chunk3267

lemma complete_chunk3268 : ∀ i : Fin 200, Compatible (653600 + i.val) →
    (table.lookup (653600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3268 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 653600 653800 :=
  FiniteIntervals.of_fin 653600 200 complete_chunk3268

lemma complete_chunk3269 : ∀ i : Fin 200, Compatible (653800 + i.val) →
    (table.lookup (653800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3269 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 653800 654000 :=
  FiniteIntervals.of_fin 653800 200 complete_chunk3269

#print axioms interval_chunk3260
end Erdos184Work.PureFiveFilter4
