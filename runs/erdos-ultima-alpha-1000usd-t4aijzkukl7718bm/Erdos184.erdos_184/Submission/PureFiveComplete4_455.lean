import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4550 : ∀ i : Fin 200, Compatible (910000 + i.val) →
    (table.lookup (910000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4550 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 910000 910200 :=
  FiniteIntervals.of_fin 910000 200 complete_chunk4550

lemma complete_chunk4551 : ∀ i : Fin 200, Compatible (910200 + i.val) →
    (table.lookup (910200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4551 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 910200 910400 :=
  FiniteIntervals.of_fin 910200 200 complete_chunk4551

lemma complete_chunk4552 : ∀ i : Fin 200, Compatible (910400 + i.val) →
    (table.lookup (910400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4552 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 910400 910600 :=
  FiniteIntervals.of_fin 910400 200 complete_chunk4552

lemma complete_chunk4553 : ∀ i : Fin 200, Compatible (910600 + i.val) →
    (table.lookup (910600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4553 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 910600 910800 :=
  FiniteIntervals.of_fin 910600 200 complete_chunk4553

lemma complete_chunk4554 : ∀ i : Fin 200, Compatible (910800 + i.val) →
    (table.lookup (910800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4554 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 910800 911000 :=
  FiniteIntervals.of_fin 910800 200 complete_chunk4554

lemma complete_chunk4555 : ∀ i : Fin 200, Compatible (911000 + i.val) →
    (table.lookup (911000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4555 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 911000 911200 :=
  FiniteIntervals.of_fin 911000 200 complete_chunk4555

lemma complete_chunk4556 : ∀ i : Fin 200, Compatible (911200 + i.val) →
    (table.lookup (911200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4556 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 911200 911400 :=
  FiniteIntervals.of_fin 911200 200 complete_chunk4556

lemma complete_chunk4557 : ∀ i : Fin 200, Compatible (911400 + i.val) →
    (table.lookup (911400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4557 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 911400 911600 :=
  FiniteIntervals.of_fin 911400 200 complete_chunk4557

lemma complete_chunk4558 : ∀ i : Fin 200, Compatible (911600 + i.val) →
    (table.lookup (911600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4558 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 911600 911800 :=
  FiniteIntervals.of_fin 911600 200 complete_chunk4558

lemma complete_chunk4559 : ∀ i : Fin 200, Compatible (911800 + i.val) →
    (table.lookup (911800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4559 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 911800 912000 :=
  FiniteIntervals.of_fin 911800 200 complete_chunk4559

#print axioms interval_chunk4550
end Erdos184Work.PureFiveFilter4
