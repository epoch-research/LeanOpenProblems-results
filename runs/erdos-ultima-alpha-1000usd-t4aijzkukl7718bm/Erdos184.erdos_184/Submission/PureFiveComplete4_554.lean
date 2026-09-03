import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5540 : ∀ i : Fin 200, Compatible (1108000 + i.val) →
    (table.lookup (1108000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5540 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1108000 1108200 :=
  FiniteIntervals.of_fin 1108000 200 complete_chunk5540

lemma complete_chunk5541 : ∀ i : Fin 200, Compatible (1108200 + i.val) →
    (table.lookup (1108200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5541 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1108200 1108400 :=
  FiniteIntervals.of_fin 1108200 200 complete_chunk5541

lemma complete_chunk5542 : ∀ i : Fin 200, Compatible (1108400 + i.val) →
    (table.lookup (1108400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5542 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1108400 1108600 :=
  FiniteIntervals.of_fin 1108400 200 complete_chunk5542

lemma complete_chunk5543 : ∀ i : Fin 200, Compatible (1108600 + i.val) →
    (table.lookup (1108600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5543 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1108600 1108800 :=
  FiniteIntervals.of_fin 1108600 200 complete_chunk5543

lemma complete_chunk5544 : ∀ i : Fin 200, Compatible (1108800 + i.val) →
    (table.lookup (1108800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5544 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1108800 1109000 :=
  FiniteIntervals.of_fin 1108800 200 complete_chunk5544

lemma complete_chunk5545 : ∀ i : Fin 200, Compatible (1109000 + i.val) →
    (table.lookup (1109000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5545 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1109000 1109200 :=
  FiniteIntervals.of_fin 1109000 200 complete_chunk5545

lemma complete_chunk5546 : ∀ i : Fin 200, Compatible (1109200 + i.val) →
    (table.lookup (1109200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5546 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1109200 1109400 :=
  FiniteIntervals.of_fin 1109200 200 complete_chunk5546

lemma complete_chunk5547 : ∀ i : Fin 200, Compatible (1109400 + i.val) →
    (table.lookup (1109400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5547 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1109400 1109600 :=
  FiniteIntervals.of_fin 1109400 200 complete_chunk5547

lemma complete_chunk5548 : ∀ i : Fin 200, Compatible (1109600 + i.val) →
    (table.lookup (1109600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5548 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1109600 1109800 :=
  FiniteIntervals.of_fin 1109600 200 complete_chunk5548

lemma complete_chunk5549 : ∀ i : Fin 200, Compatible (1109800 + i.val) →
    (table.lookup (1109800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5549 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1109800 1110000 :=
  FiniteIntervals.of_fin 1109800 200 complete_chunk5549

#print axioms interval_chunk5540
end Erdos184Work.PureFiveFilter4
