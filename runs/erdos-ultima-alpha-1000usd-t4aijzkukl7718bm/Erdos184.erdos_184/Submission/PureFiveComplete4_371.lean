import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3710 : ∀ i : Fin 200, Compatible (742000 + i.val) →
    (table.lookup (742000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3710 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 742000 742200 :=
  FiniteIntervals.of_fin 742000 200 complete_chunk3710

lemma complete_chunk3711 : ∀ i : Fin 200, Compatible (742200 + i.val) →
    (table.lookup (742200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3711 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 742200 742400 :=
  FiniteIntervals.of_fin 742200 200 complete_chunk3711

lemma complete_chunk3712 : ∀ i : Fin 200, Compatible (742400 + i.val) →
    (table.lookup (742400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3712 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 742400 742600 :=
  FiniteIntervals.of_fin 742400 200 complete_chunk3712

lemma complete_chunk3713 : ∀ i : Fin 200, Compatible (742600 + i.val) →
    (table.lookup (742600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3713 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 742600 742800 :=
  FiniteIntervals.of_fin 742600 200 complete_chunk3713

lemma complete_chunk3714 : ∀ i : Fin 200, Compatible (742800 + i.val) →
    (table.lookup (742800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3714 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 742800 743000 :=
  FiniteIntervals.of_fin 742800 200 complete_chunk3714

lemma complete_chunk3715 : ∀ i : Fin 200, Compatible (743000 + i.val) →
    (table.lookup (743000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3715 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 743000 743200 :=
  FiniteIntervals.of_fin 743000 200 complete_chunk3715

lemma complete_chunk3716 : ∀ i : Fin 200, Compatible (743200 + i.val) →
    (table.lookup (743200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3716 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 743200 743400 :=
  FiniteIntervals.of_fin 743200 200 complete_chunk3716

lemma complete_chunk3717 : ∀ i : Fin 200, Compatible (743400 + i.val) →
    (table.lookup (743400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3717 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 743400 743600 :=
  FiniteIntervals.of_fin 743400 200 complete_chunk3717

lemma complete_chunk3718 : ∀ i : Fin 200, Compatible (743600 + i.val) →
    (table.lookup (743600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3718 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 743600 743800 :=
  FiniteIntervals.of_fin 743600 200 complete_chunk3718

lemma complete_chunk3719 : ∀ i : Fin 200, Compatible (743800 + i.val) →
    (table.lookup (743800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3719 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 743800 744000 :=
  FiniteIntervals.of_fin 743800 200 complete_chunk3719

#print axioms interval_chunk3710
end Erdos184Work.PureFiveFilter4
