import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2400 : ∀ i : Fin 200, Compatible (480000 + i.val) →
    (table.lookup (480000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2400 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 480000 480200 :=
  FiniteIntervals.of_fin 480000 200 complete_chunk2400

lemma complete_chunk2401 : ∀ i : Fin 200, Compatible (480200 + i.val) →
    (table.lookup (480200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2401 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 480200 480400 :=
  FiniteIntervals.of_fin 480200 200 complete_chunk2401

lemma complete_chunk2402 : ∀ i : Fin 200, Compatible (480400 + i.val) →
    (table.lookup (480400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2402 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 480400 480600 :=
  FiniteIntervals.of_fin 480400 200 complete_chunk2402

lemma complete_chunk2403 : ∀ i : Fin 200, Compatible (480600 + i.val) →
    (table.lookup (480600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2403 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 480600 480800 :=
  FiniteIntervals.of_fin 480600 200 complete_chunk2403

lemma complete_chunk2404 : ∀ i : Fin 200, Compatible (480800 + i.val) →
    (table.lookup (480800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2404 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 480800 481000 :=
  FiniteIntervals.of_fin 480800 200 complete_chunk2404

lemma complete_chunk2405 : ∀ i : Fin 200, Compatible (481000 + i.val) →
    (table.lookup (481000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2405 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 481000 481200 :=
  FiniteIntervals.of_fin 481000 200 complete_chunk2405

lemma complete_chunk2406 : ∀ i : Fin 200, Compatible (481200 + i.val) →
    (table.lookup (481200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2406 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 481200 481400 :=
  FiniteIntervals.of_fin 481200 200 complete_chunk2406

lemma complete_chunk2407 : ∀ i : Fin 200, Compatible (481400 + i.val) →
    (table.lookup (481400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2407 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 481400 481600 :=
  FiniteIntervals.of_fin 481400 200 complete_chunk2407

lemma complete_chunk2408 : ∀ i : Fin 200, Compatible (481600 + i.val) →
    (table.lookup (481600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2408 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 481600 481800 :=
  FiniteIntervals.of_fin 481600 200 complete_chunk2408

lemma complete_chunk2409 : ∀ i : Fin 200, Compatible (481800 + i.val) →
    (table.lookup (481800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2409 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 481800 482000 :=
  FiniteIntervals.of_fin 481800 200 complete_chunk2409

#print axioms interval_chunk2400
end Erdos184Work.PureFiveFilter4
