import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4330 : ∀ i : Fin 200, Compatible (866000 + i.val) →
    (table.lookup (866000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4330 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 866000 866200 :=
  FiniteIntervals.of_fin 866000 200 complete_chunk4330

lemma complete_chunk4331 : ∀ i : Fin 200, Compatible (866200 + i.val) →
    (table.lookup (866200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4331 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 866200 866400 :=
  FiniteIntervals.of_fin 866200 200 complete_chunk4331

lemma complete_chunk4332 : ∀ i : Fin 200, Compatible (866400 + i.val) →
    (table.lookup (866400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4332 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 866400 866600 :=
  FiniteIntervals.of_fin 866400 200 complete_chunk4332

lemma complete_chunk4333 : ∀ i : Fin 200, Compatible (866600 + i.val) →
    (table.lookup (866600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4333 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 866600 866800 :=
  FiniteIntervals.of_fin 866600 200 complete_chunk4333

lemma complete_chunk4334 : ∀ i : Fin 200, Compatible (866800 + i.val) →
    (table.lookup (866800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4334 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 866800 867000 :=
  FiniteIntervals.of_fin 866800 200 complete_chunk4334

lemma complete_chunk4335 : ∀ i : Fin 200, Compatible (867000 + i.val) →
    (table.lookup (867000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4335 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 867000 867200 :=
  FiniteIntervals.of_fin 867000 200 complete_chunk4335

lemma complete_chunk4336 : ∀ i : Fin 200, Compatible (867200 + i.val) →
    (table.lookup (867200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4336 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 867200 867400 :=
  FiniteIntervals.of_fin 867200 200 complete_chunk4336

lemma complete_chunk4337 : ∀ i : Fin 200, Compatible (867400 + i.val) →
    (table.lookup (867400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4337 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 867400 867600 :=
  FiniteIntervals.of_fin 867400 200 complete_chunk4337

lemma complete_chunk4338 : ∀ i : Fin 200, Compatible (867600 + i.val) →
    (table.lookup (867600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4338 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 867600 867800 :=
  FiniteIntervals.of_fin 867600 200 complete_chunk4338

lemma complete_chunk4339 : ∀ i : Fin 200, Compatible (867800 + i.val) →
    (table.lookup (867800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4339 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 867800 868000 :=
  FiniteIntervals.of_fin 867800 200 complete_chunk4339

#print axioms interval_chunk4330
end Erdos184Work.PureFiveFilter4
