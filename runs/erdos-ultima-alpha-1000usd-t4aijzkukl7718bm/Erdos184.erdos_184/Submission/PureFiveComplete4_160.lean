import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1600 : ∀ i : Fin 200, Compatible (320000 + i.val) →
    (table.lookup (320000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1600 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 320000 320200 :=
  FiniteIntervals.of_fin 320000 200 complete_chunk1600

lemma complete_chunk1601 : ∀ i : Fin 200, Compatible (320200 + i.val) →
    (table.lookup (320200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1601 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 320200 320400 :=
  FiniteIntervals.of_fin 320200 200 complete_chunk1601

lemma complete_chunk1602 : ∀ i : Fin 200, Compatible (320400 + i.val) →
    (table.lookup (320400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1602 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 320400 320600 :=
  FiniteIntervals.of_fin 320400 200 complete_chunk1602

lemma complete_chunk1603 : ∀ i : Fin 200, Compatible (320600 + i.val) →
    (table.lookup (320600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1603 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 320600 320800 :=
  FiniteIntervals.of_fin 320600 200 complete_chunk1603

lemma complete_chunk1604 : ∀ i : Fin 200, Compatible (320800 + i.val) →
    (table.lookup (320800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1604 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 320800 321000 :=
  FiniteIntervals.of_fin 320800 200 complete_chunk1604

lemma complete_chunk1605 : ∀ i : Fin 200, Compatible (321000 + i.val) →
    (table.lookup (321000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1605 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 321000 321200 :=
  FiniteIntervals.of_fin 321000 200 complete_chunk1605

lemma complete_chunk1606 : ∀ i : Fin 200, Compatible (321200 + i.val) →
    (table.lookup (321200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1606 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 321200 321400 :=
  FiniteIntervals.of_fin 321200 200 complete_chunk1606

lemma complete_chunk1607 : ∀ i : Fin 200, Compatible (321400 + i.val) →
    (table.lookup (321400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1607 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 321400 321600 :=
  FiniteIntervals.of_fin 321400 200 complete_chunk1607

lemma complete_chunk1608 : ∀ i : Fin 200, Compatible (321600 + i.val) →
    (table.lookup (321600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1608 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 321600 321800 :=
  FiniteIntervals.of_fin 321600 200 complete_chunk1608

lemma complete_chunk1609 : ∀ i : Fin 200, Compatible (321800 + i.val) →
    (table.lookup (321800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1609 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 321800 322000 :=
  FiniteIntervals.of_fin 321800 200 complete_chunk1609

#print axioms interval_chunk1600
end Erdos184Work.PureFiveFilter4
