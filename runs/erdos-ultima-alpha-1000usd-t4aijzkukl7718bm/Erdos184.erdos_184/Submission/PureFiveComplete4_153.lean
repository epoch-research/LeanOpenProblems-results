import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1530 : ∀ i : Fin 200, Compatible (306000 + i.val) →
    (table.lookup (306000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1530 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 306000 306200 :=
  FiniteIntervals.of_fin 306000 200 complete_chunk1530

lemma complete_chunk1531 : ∀ i : Fin 200, Compatible (306200 + i.val) →
    (table.lookup (306200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1531 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 306200 306400 :=
  FiniteIntervals.of_fin 306200 200 complete_chunk1531

lemma complete_chunk1532 : ∀ i : Fin 200, Compatible (306400 + i.val) →
    (table.lookup (306400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1532 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 306400 306600 :=
  FiniteIntervals.of_fin 306400 200 complete_chunk1532

lemma complete_chunk1533 : ∀ i : Fin 200, Compatible (306600 + i.val) →
    (table.lookup (306600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1533 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 306600 306800 :=
  FiniteIntervals.of_fin 306600 200 complete_chunk1533

lemma complete_chunk1534 : ∀ i : Fin 200, Compatible (306800 + i.val) →
    (table.lookup (306800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1534 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 306800 307000 :=
  FiniteIntervals.of_fin 306800 200 complete_chunk1534

lemma complete_chunk1535 : ∀ i : Fin 200, Compatible (307000 + i.val) →
    (table.lookup (307000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1535 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 307000 307200 :=
  FiniteIntervals.of_fin 307000 200 complete_chunk1535

lemma complete_chunk1536 : ∀ i : Fin 200, Compatible (307200 + i.val) →
    (table.lookup (307200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1536 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 307200 307400 :=
  FiniteIntervals.of_fin 307200 200 complete_chunk1536

lemma complete_chunk1537 : ∀ i : Fin 200, Compatible (307400 + i.val) →
    (table.lookup (307400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1537 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 307400 307600 :=
  FiniteIntervals.of_fin 307400 200 complete_chunk1537

lemma complete_chunk1538 : ∀ i : Fin 200, Compatible (307600 + i.val) →
    (table.lookup (307600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1538 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 307600 307800 :=
  FiniteIntervals.of_fin 307600 200 complete_chunk1538

lemma complete_chunk1539 : ∀ i : Fin 200, Compatible (307800 + i.val) →
    (table.lookup (307800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1539 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 307800 308000 :=
  FiniteIntervals.of_fin 307800 200 complete_chunk1539

#print axioms interval_chunk1530
end Erdos184Work.PureFiveFilter4
