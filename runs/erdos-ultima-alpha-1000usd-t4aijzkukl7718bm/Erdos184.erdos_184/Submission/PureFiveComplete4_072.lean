import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk720 : ∀ i : Fin 200, Compatible (144000 + i.val) →
    (table.lookup (144000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk720 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 144000 144200 :=
  FiniteIntervals.of_fin 144000 200 complete_chunk720

lemma complete_chunk721 : ∀ i : Fin 200, Compatible (144200 + i.val) →
    (table.lookup (144200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk721 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 144200 144400 :=
  FiniteIntervals.of_fin 144200 200 complete_chunk721

lemma complete_chunk722 : ∀ i : Fin 200, Compatible (144400 + i.val) →
    (table.lookup (144400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk722 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 144400 144600 :=
  FiniteIntervals.of_fin 144400 200 complete_chunk722

lemma complete_chunk723 : ∀ i : Fin 200, Compatible (144600 + i.val) →
    (table.lookup (144600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk723 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 144600 144800 :=
  FiniteIntervals.of_fin 144600 200 complete_chunk723

lemma complete_chunk724 : ∀ i : Fin 200, Compatible (144800 + i.val) →
    (table.lookup (144800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk724 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 144800 145000 :=
  FiniteIntervals.of_fin 144800 200 complete_chunk724

lemma complete_chunk725 : ∀ i : Fin 200, Compatible (145000 + i.val) →
    (table.lookup (145000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk725 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 145000 145200 :=
  FiniteIntervals.of_fin 145000 200 complete_chunk725

lemma complete_chunk726 : ∀ i : Fin 200, Compatible (145200 + i.val) →
    (table.lookup (145200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk726 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 145200 145400 :=
  FiniteIntervals.of_fin 145200 200 complete_chunk726

lemma complete_chunk727 : ∀ i : Fin 200, Compatible (145400 + i.val) →
    (table.lookup (145400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk727 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 145400 145600 :=
  FiniteIntervals.of_fin 145400 200 complete_chunk727

lemma complete_chunk728 : ∀ i : Fin 200, Compatible (145600 + i.val) →
    (table.lookup (145600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk728 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 145600 145800 :=
  FiniteIntervals.of_fin 145600 200 complete_chunk728

lemma complete_chunk729 : ∀ i : Fin 200, Compatible (145800 + i.val) →
    (table.lookup (145800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk729 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 145800 146000 :=
  FiniteIntervals.of_fin 145800 200 complete_chunk729

#print axioms interval_chunk720
end Erdos184Work.PureFiveFilter4
