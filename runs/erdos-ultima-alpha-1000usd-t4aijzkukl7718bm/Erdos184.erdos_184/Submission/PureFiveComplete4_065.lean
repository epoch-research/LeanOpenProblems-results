import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk650 : ∀ i : Fin 200, Compatible (130000 + i.val) →
    (table.lookup (130000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk650 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 130000 130200 :=
  FiniteIntervals.of_fin 130000 200 complete_chunk650

lemma complete_chunk651 : ∀ i : Fin 200, Compatible (130200 + i.val) →
    (table.lookup (130200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk651 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 130200 130400 :=
  FiniteIntervals.of_fin 130200 200 complete_chunk651

lemma complete_chunk652 : ∀ i : Fin 200, Compatible (130400 + i.val) →
    (table.lookup (130400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk652 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 130400 130600 :=
  FiniteIntervals.of_fin 130400 200 complete_chunk652

lemma complete_chunk653 : ∀ i : Fin 200, Compatible (130600 + i.val) →
    (table.lookup (130600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk653 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 130600 130800 :=
  FiniteIntervals.of_fin 130600 200 complete_chunk653

lemma complete_chunk654 : ∀ i : Fin 200, Compatible (130800 + i.val) →
    (table.lookup (130800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk654 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 130800 131000 :=
  FiniteIntervals.of_fin 130800 200 complete_chunk654

lemma complete_chunk655 : ∀ i : Fin 200, Compatible (131000 + i.val) →
    (table.lookup (131000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk655 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 131000 131200 :=
  FiniteIntervals.of_fin 131000 200 complete_chunk655

lemma complete_chunk656 : ∀ i : Fin 200, Compatible (131200 + i.val) →
    (table.lookup (131200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk656 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 131200 131400 :=
  FiniteIntervals.of_fin 131200 200 complete_chunk656

lemma complete_chunk657 : ∀ i : Fin 200, Compatible (131400 + i.val) →
    (table.lookup (131400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk657 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 131400 131600 :=
  FiniteIntervals.of_fin 131400 200 complete_chunk657

lemma complete_chunk658 : ∀ i : Fin 200, Compatible (131600 + i.val) →
    (table.lookup (131600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk658 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 131600 131800 :=
  FiniteIntervals.of_fin 131600 200 complete_chunk658

lemma complete_chunk659 : ∀ i : Fin 200, Compatible (131800 + i.val) →
    (table.lookup (131800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk659 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 131800 132000 :=
  FiniteIntervals.of_fin 131800 200 complete_chunk659

#print axioms interval_chunk650
end Erdos184Work.PureFiveFilter4
