import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4540 : ∀ i : Fin 200, Compatible (908000 + i.val) →
    (table.lookup (908000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4540 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 908000 908200 :=
  FiniteIntervals.of_fin 908000 200 complete_chunk4540

lemma complete_chunk4541 : ∀ i : Fin 200, Compatible (908200 + i.val) →
    (table.lookup (908200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4541 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 908200 908400 :=
  FiniteIntervals.of_fin 908200 200 complete_chunk4541

lemma complete_chunk4542 : ∀ i : Fin 200, Compatible (908400 + i.val) →
    (table.lookup (908400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4542 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 908400 908600 :=
  FiniteIntervals.of_fin 908400 200 complete_chunk4542

lemma complete_chunk4543 : ∀ i : Fin 200, Compatible (908600 + i.val) →
    (table.lookup (908600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4543 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 908600 908800 :=
  FiniteIntervals.of_fin 908600 200 complete_chunk4543

lemma complete_chunk4544 : ∀ i : Fin 200, Compatible (908800 + i.val) →
    (table.lookup (908800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4544 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 908800 909000 :=
  FiniteIntervals.of_fin 908800 200 complete_chunk4544

lemma complete_chunk4545 : ∀ i : Fin 200, Compatible (909000 + i.val) →
    (table.lookup (909000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4545 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 909000 909200 :=
  FiniteIntervals.of_fin 909000 200 complete_chunk4545

lemma complete_chunk4546 : ∀ i : Fin 200, Compatible (909200 + i.val) →
    (table.lookup (909200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4546 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 909200 909400 :=
  FiniteIntervals.of_fin 909200 200 complete_chunk4546

lemma complete_chunk4547 : ∀ i : Fin 200, Compatible (909400 + i.val) →
    (table.lookup (909400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4547 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 909400 909600 :=
  FiniteIntervals.of_fin 909400 200 complete_chunk4547

lemma complete_chunk4548 : ∀ i : Fin 200, Compatible (909600 + i.val) →
    (table.lookup (909600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4548 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 909600 909800 :=
  FiniteIntervals.of_fin 909600 200 complete_chunk4548

lemma complete_chunk4549 : ∀ i : Fin 200, Compatible (909800 + i.val) →
    (table.lookup (909800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4549 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 909800 910000 :=
  FiniteIntervals.of_fin 909800 200 complete_chunk4549

#print axioms interval_chunk4540
end Erdos184Work.PureFiveFilter4
