import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1630 : ∀ i : Fin 200, Compatible (326000 + i.val) →
    (table.lookup (326000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1630 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 326000 326200 :=
  FiniteIntervals.of_fin 326000 200 complete_chunk1630

lemma complete_chunk1631 : ∀ i : Fin 200, Compatible (326200 + i.val) →
    (table.lookup (326200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1631 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 326200 326400 :=
  FiniteIntervals.of_fin 326200 200 complete_chunk1631

lemma complete_chunk1632 : ∀ i : Fin 200, Compatible (326400 + i.val) →
    (table.lookup (326400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1632 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 326400 326600 :=
  FiniteIntervals.of_fin 326400 200 complete_chunk1632

lemma complete_chunk1633 : ∀ i : Fin 200, Compatible (326600 + i.val) →
    (table.lookup (326600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1633 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 326600 326800 :=
  FiniteIntervals.of_fin 326600 200 complete_chunk1633

lemma complete_chunk1634 : ∀ i : Fin 200, Compatible (326800 + i.val) →
    (table.lookup (326800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1634 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 326800 327000 :=
  FiniteIntervals.of_fin 326800 200 complete_chunk1634

lemma complete_chunk1635 : ∀ i : Fin 200, Compatible (327000 + i.val) →
    (table.lookup (327000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1635 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 327000 327200 :=
  FiniteIntervals.of_fin 327000 200 complete_chunk1635

lemma complete_chunk1636 : ∀ i : Fin 200, Compatible (327200 + i.val) →
    (table.lookup (327200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1636 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 327200 327400 :=
  FiniteIntervals.of_fin 327200 200 complete_chunk1636

lemma complete_chunk1637 : ∀ i : Fin 200, Compatible (327400 + i.val) →
    (table.lookup (327400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1637 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 327400 327600 :=
  FiniteIntervals.of_fin 327400 200 complete_chunk1637

lemma complete_chunk1638 : ∀ i : Fin 200, Compatible (327600 + i.val) →
    (table.lookup (327600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1638 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 327600 327800 :=
  FiniteIntervals.of_fin 327600 200 complete_chunk1638

lemma complete_chunk1639 : ∀ i : Fin 200, Compatible (327800 + i.val) →
    (table.lookup (327800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1639 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 327800 328000 :=
  FiniteIntervals.of_fin 327800 200 complete_chunk1639

#print axioms interval_chunk1630
end Erdos184Work.PureFiveFilter4
