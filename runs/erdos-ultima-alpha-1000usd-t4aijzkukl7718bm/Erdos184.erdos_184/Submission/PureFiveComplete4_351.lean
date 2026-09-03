import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3510 : ∀ i : Fin 200, Compatible (702000 + i.val) →
    (table.lookup (702000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3510 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 702000 702200 :=
  FiniteIntervals.of_fin 702000 200 complete_chunk3510

lemma complete_chunk3511 : ∀ i : Fin 200, Compatible (702200 + i.val) →
    (table.lookup (702200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3511 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 702200 702400 :=
  FiniteIntervals.of_fin 702200 200 complete_chunk3511

lemma complete_chunk3512 : ∀ i : Fin 200, Compatible (702400 + i.val) →
    (table.lookup (702400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3512 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 702400 702600 :=
  FiniteIntervals.of_fin 702400 200 complete_chunk3512

lemma complete_chunk3513 : ∀ i : Fin 200, Compatible (702600 + i.val) →
    (table.lookup (702600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3513 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 702600 702800 :=
  FiniteIntervals.of_fin 702600 200 complete_chunk3513

lemma complete_chunk3514 : ∀ i : Fin 200, Compatible (702800 + i.val) →
    (table.lookup (702800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3514 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 702800 703000 :=
  FiniteIntervals.of_fin 702800 200 complete_chunk3514

lemma complete_chunk3515 : ∀ i : Fin 200, Compatible (703000 + i.val) →
    (table.lookup (703000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3515 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 703000 703200 :=
  FiniteIntervals.of_fin 703000 200 complete_chunk3515

lemma complete_chunk3516 : ∀ i : Fin 200, Compatible (703200 + i.val) →
    (table.lookup (703200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3516 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 703200 703400 :=
  FiniteIntervals.of_fin 703200 200 complete_chunk3516

lemma complete_chunk3517 : ∀ i : Fin 200, Compatible (703400 + i.val) →
    (table.lookup (703400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3517 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 703400 703600 :=
  FiniteIntervals.of_fin 703400 200 complete_chunk3517

lemma complete_chunk3518 : ∀ i : Fin 200, Compatible (703600 + i.val) →
    (table.lookup (703600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3518 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 703600 703800 :=
  FiniteIntervals.of_fin 703600 200 complete_chunk3518

lemma complete_chunk3519 : ∀ i : Fin 200, Compatible (703800 + i.val) →
    (table.lookup (703800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3519 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 703800 704000 :=
  FiniteIntervals.of_fin 703800 200 complete_chunk3519

#print axioms interval_chunk3510
end Erdos184Work.PureFiveFilter4
