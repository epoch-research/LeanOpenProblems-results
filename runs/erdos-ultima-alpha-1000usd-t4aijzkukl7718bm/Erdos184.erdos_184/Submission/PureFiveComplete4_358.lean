import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3580 : ∀ i : Fin 200, Compatible (716000 + i.val) →
    (table.lookup (716000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3580 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 716000 716200 :=
  FiniteIntervals.of_fin 716000 200 complete_chunk3580

lemma complete_chunk3581 : ∀ i : Fin 200, Compatible (716200 + i.val) →
    (table.lookup (716200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3581 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 716200 716400 :=
  FiniteIntervals.of_fin 716200 200 complete_chunk3581

lemma complete_chunk3582 : ∀ i : Fin 200, Compatible (716400 + i.val) →
    (table.lookup (716400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3582 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 716400 716600 :=
  FiniteIntervals.of_fin 716400 200 complete_chunk3582

lemma complete_chunk3583 : ∀ i : Fin 200, Compatible (716600 + i.val) →
    (table.lookup (716600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3583 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 716600 716800 :=
  FiniteIntervals.of_fin 716600 200 complete_chunk3583

lemma complete_chunk3584 : ∀ i : Fin 200, Compatible (716800 + i.val) →
    (table.lookup (716800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3584 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 716800 717000 :=
  FiniteIntervals.of_fin 716800 200 complete_chunk3584

lemma complete_chunk3585 : ∀ i : Fin 200, Compatible (717000 + i.val) →
    (table.lookup (717000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3585 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 717000 717200 :=
  FiniteIntervals.of_fin 717000 200 complete_chunk3585

lemma complete_chunk3586 : ∀ i : Fin 200, Compatible (717200 + i.val) →
    (table.lookup (717200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3586 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 717200 717400 :=
  FiniteIntervals.of_fin 717200 200 complete_chunk3586

lemma complete_chunk3587 : ∀ i : Fin 200, Compatible (717400 + i.val) →
    (table.lookup (717400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3587 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 717400 717600 :=
  FiniteIntervals.of_fin 717400 200 complete_chunk3587

lemma complete_chunk3588 : ∀ i : Fin 200, Compatible (717600 + i.val) →
    (table.lookup (717600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3588 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 717600 717800 :=
  FiniteIntervals.of_fin 717600 200 complete_chunk3588

lemma complete_chunk3589 : ∀ i : Fin 200, Compatible (717800 + i.val) →
    (table.lookup (717800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3589 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 717800 718000 :=
  FiniteIntervals.of_fin 717800 200 complete_chunk3589

#print axioms interval_chunk3580
end Erdos184Work.PureFiveFilter4
