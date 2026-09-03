import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3670 : ∀ i : Fin 200, Compatible (734000 + i.val) →
    (table.lookup (734000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3670 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 734000 734200 :=
  FiniteIntervals.of_fin 734000 200 complete_chunk3670

lemma complete_chunk3671 : ∀ i : Fin 200, Compatible (734200 + i.val) →
    (table.lookup (734200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3671 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 734200 734400 :=
  FiniteIntervals.of_fin 734200 200 complete_chunk3671

lemma complete_chunk3672 : ∀ i : Fin 200, Compatible (734400 + i.val) →
    (table.lookup (734400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3672 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 734400 734600 :=
  FiniteIntervals.of_fin 734400 200 complete_chunk3672

lemma complete_chunk3673 : ∀ i : Fin 200, Compatible (734600 + i.val) →
    (table.lookup (734600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3673 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 734600 734800 :=
  FiniteIntervals.of_fin 734600 200 complete_chunk3673

lemma complete_chunk3674 : ∀ i : Fin 200, Compatible (734800 + i.val) →
    (table.lookup (734800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3674 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 734800 735000 :=
  FiniteIntervals.of_fin 734800 200 complete_chunk3674

lemma complete_chunk3675 : ∀ i : Fin 200, Compatible (735000 + i.val) →
    (table.lookup (735000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3675 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 735000 735200 :=
  FiniteIntervals.of_fin 735000 200 complete_chunk3675

lemma complete_chunk3676 : ∀ i : Fin 200, Compatible (735200 + i.val) →
    (table.lookup (735200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3676 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 735200 735400 :=
  FiniteIntervals.of_fin 735200 200 complete_chunk3676

lemma complete_chunk3677 : ∀ i : Fin 200, Compatible (735400 + i.val) →
    (table.lookup (735400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3677 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 735400 735600 :=
  FiniteIntervals.of_fin 735400 200 complete_chunk3677

lemma complete_chunk3678 : ∀ i : Fin 200, Compatible (735600 + i.val) →
    (table.lookup (735600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3678 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 735600 735800 :=
  FiniteIntervals.of_fin 735600 200 complete_chunk3678

lemma complete_chunk3679 : ∀ i : Fin 200, Compatible (735800 + i.val) →
    (table.lookup (735800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3679 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 735800 736000 :=
  FiniteIntervals.of_fin 735800 200 complete_chunk3679

#print axioms interval_chunk3670
end Erdos184Work.PureFiveFilter4
