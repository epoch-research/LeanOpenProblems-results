import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5400 : ∀ i : Fin 200, Compatible (1080000 + i.val) →
    (table.lookup (1080000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5400 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1080000 1080200 :=
  FiniteIntervals.of_fin 1080000 200 complete_chunk5400

lemma complete_chunk5401 : ∀ i : Fin 200, Compatible (1080200 + i.val) →
    (table.lookup (1080200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5401 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1080200 1080400 :=
  FiniteIntervals.of_fin 1080200 200 complete_chunk5401

lemma complete_chunk5402 : ∀ i : Fin 200, Compatible (1080400 + i.val) →
    (table.lookup (1080400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5402 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1080400 1080600 :=
  FiniteIntervals.of_fin 1080400 200 complete_chunk5402

lemma complete_chunk5403 : ∀ i : Fin 200, Compatible (1080600 + i.val) →
    (table.lookup (1080600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5403 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1080600 1080800 :=
  FiniteIntervals.of_fin 1080600 200 complete_chunk5403

lemma complete_chunk5404 : ∀ i : Fin 200, Compatible (1080800 + i.val) →
    (table.lookup (1080800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5404 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1080800 1081000 :=
  FiniteIntervals.of_fin 1080800 200 complete_chunk5404

lemma complete_chunk5405 : ∀ i : Fin 200, Compatible (1081000 + i.val) →
    (table.lookup (1081000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5405 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1081000 1081200 :=
  FiniteIntervals.of_fin 1081000 200 complete_chunk5405

lemma complete_chunk5406 : ∀ i : Fin 200, Compatible (1081200 + i.val) →
    (table.lookup (1081200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5406 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1081200 1081400 :=
  FiniteIntervals.of_fin 1081200 200 complete_chunk5406

lemma complete_chunk5407 : ∀ i : Fin 200, Compatible (1081400 + i.val) →
    (table.lookup (1081400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5407 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1081400 1081600 :=
  FiniteIntervals.of_fin 1081400 200 complete_chunk5407

lemma complete_chunk5408 : ∀ i : Fin 200, Compatible (1081600 + i.val) →
    (table.lookup (1081600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5408 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1081600 1081800 :=
  FiniteIntervals.of_fin 1081600 200 complete_chunk5408

lemma complete_chunk5409 : ∀ i : Fin 200, Compatible (1081800 + i.val) →
    (table.lookup (1081800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5409 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1081800 1082000 :=
  FiniteIntervals.of_fin 1081800 200 complete_chunk5409

#print axioms interval_chunk5400
end Erdos184Work.PureFiveFilter4
