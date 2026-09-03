import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4650 : ∀ i : Fin 200, Compatible (930000 + i.val) →
    (table.lookup (930000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4650 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 930000 930200 :=
  FiniteIntervals.of_fin 930000 200 complete_chunk4650

lemma complete_chunk4651 : ∀ i : Fin 200, Compatible (930200 + i.val) →
    (table.lookup (930200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4651 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 930200 930400 :=
  FiniteIntervals.of_fin 930200 200 complete_chunk4651

lemma complete_chunk4652 : ∀ i : Fin 200, Compatible (930400 + i.val) →
    (table.lookup (930400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4652 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 930400 930600 :=
  FiniteIntervals.of_fin 930400 200 complete_chunk4652

lemma complete_chunk4653 : ∀ i : Fin 200, Compatible (930600 + i.val) →
    (table.lookup (930600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4653 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 930600 930800 :=
  FiniteIntervals.of_fin 930600 200 complete_chunk4653

lemma complete_chunk4654 : ∀ i : Fin 200, Compatible (930800 + i.val) →
    (table.lookup (930800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4654 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 930800 931000 :=
  FiniteIntervals.of_fin 930800 200 complete_chunk4654

lemma complete_chunk4655 : ∀ i : Fin 200, Compatible (931000 + i.val) →
    (table.lookup (931000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4655 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 931000 931200 :=
  FiniteIntervals.of_fin 931000 200 complete_chunk4655

lemma complete_chunk4656 : ∀ i : Fin 200, Compatible (931200 + i.val) →
    (table.lookup (931200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4656 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 931200 931400 :=
  FiniteIntervals.of_fin 931200 200 complete_chunk4656

lemma complete_chunk4657 : ∀ i : Fin 200, Compatible (931400 + i.val) →
    (table.lookup (931400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4657 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 931400 931600 :=
  FiniteIntervals.of_fin 931400 200 complete_chunk4657

lemma complete_chunk4658 : ∀ i : Fin 200, Compatible (931600 + i.val) →
    (table.lookup (931600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4658 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 931600 931800 :=
  FiniteIntervals.of_fin 931600 200 complete_chunk4658

lemma complete_chunk4659 : ∀ i : Fin 200, Compatible (931800 + i.val) →
    (table.lookup (931800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4659 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 931800 932000 :=
  FiniteIntervals.of_fin 931800 200 complete_chunk4659

#print axioms interval_chunk4650
end Erdos184Work.PureFiveFilter4
