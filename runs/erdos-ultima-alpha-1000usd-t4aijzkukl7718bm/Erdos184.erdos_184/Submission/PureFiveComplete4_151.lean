import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1510 : ∀ i : Fin 200, Compatible (302000 + i.val) →
    (table.lookup (302000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1510 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 302000 302200 :=
  FiniteIntervals.of_fin 302000 200 complete_chunk1510

lemma complete_chunk1511 : ∀ i : Fin 200, Compatible (302200 + i.val) →
    (table.lookup (302200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1511 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 302200 302400 :=
  FiniteIntervals.of_fin 302200 200 complete_chunk1511

lemma complete_chunk1512 : ∀ i : Fin 200, Compatible (302400 + i.val) →
    (table.lookup (302400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1512 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 302400 302600 :=
  FiniteIntervals.of_fin 302400 200 complete_chunk1512

lemma complete_chunk1513 : ∀ i : Fin 200, Compatible (302600 + i.val) →
    (table.lookup (302600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1513 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 302600 302800 :=
  FiniteIntervals.of_fin 302600 200 complete_chunk1513

lemma complete_chunk1514 : ∀ i : Fin 200, Compatible (302800 + i.val) →
    (table.lookup (302800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1514 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 302800 303000 :=
  FiniteIntervals.of_fin 302800 200 complete_chunk1514

lemma complete_chunk1515 : ∀ i : Fin 200, Compatible (303000 + i.val) →
    (table.lookup (303000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1515 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 303000 303200 :=
  FiniteIntervals.of_fin 303000 200 complete_chunk1515

lemma complete_chunk1516 : ∀ i : Fin 200, Compatible (303200 + i.val) →
    (table.lookup (303200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1516 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 303200 303400 :=
  FiniteIntervals.of_fin 303200 200 complete_chunk1516

lemma complete_chunk1517 : ∀ i : Fin 200, Compatible (303400 + i.val) →
    (table.lookup (303400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1517 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 303400 303600 :=
  FiniteIntervals.of_fin 303400 200 complete_chunk1517

lemma complete_chunk1518 : ∀ i : Fin 200, Compatible (303600 + i.val) →
    (table.lookup (303600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1518 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 303600 303800 :=
  FiniteIntervals.of_fin 303600 200 complete_chunk1518

lemma complete_chunk1519 : ∀ i : Fin 200, Compatible (303800 + i.val) →
    (table.lookup (303800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1519 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 303800 304000 :=
  FiniteIntervals.of_fin 303800 200 complete_chunk1519

#print axioms interval_chunk1510
end Erdos184Work.PureFiveFilter4
