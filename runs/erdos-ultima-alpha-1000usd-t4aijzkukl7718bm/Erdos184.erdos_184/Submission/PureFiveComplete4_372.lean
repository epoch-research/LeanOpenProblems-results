import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3720 : ∀ i : Fin 200, Compatible (744000 + i.val) →
    (table.lookup (744000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3720 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 744000 744200 :=
  FiniteIntervals.of_fin 744000 200 complete_chunk3720

lemma complete_chunk3721 : ∀ i : Fin 200, Compatible (744200 + i.val) →
    (table.lookup (744200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3721 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 744200 744400 :=
  FiniteIntervals.of_fin 744200 200 complete_chunk3721

lemma complete_chunk3722 : ∀ i : Fin 200, Compatible (744400 + i.val) →
    (table.lookup (744400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3722 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 744400 744600 :=
  FiniteIntervals.of_fin 744400 200 complete_chunk3722

lemma complete_chunk3723 : ∀ i : Fin 200, Compatible (744600 + i.val) →
    (table.lookup (744600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3723 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 744600 744800 :=
  FiniteIntervals.of_fin 744600 200 complete_chunk3723

lemma complete_chunk3724 : ∀ i : Fin 200, Compatible (744800 + i.val) →
    (table.lookup (744800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3724 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 744800 745000 :=
  FiniteIntervals.of_fin 744800 200 complete_chunk3724

lemma complete_chunk3725 : ∀ i : Fin 200, Compatible (745000 + i.val) →
    (table.lookup (745000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3725 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 745000 745200 :=
  FiniteIntervals.of_fin 745000 200 complete_chunk3725

lemma complete_chunk3726 : ∀ i : Fin 200, Compatible (745200 + i.val) →
    (table.lookup (745200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3726 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 745200 745400 :=
  FiniteIntervals.of_fin 745200 200 complete_chunk3726

lemma complete_chunk3727 : ∀ i : Fin 200, Compatible (745400 + i.val) →
    (table.lookup (745400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3727 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 745400 745600 :=
  FiniteIntervals.of_fin 745400 200 complete_chunk3727

lemma complete_chunk3728 : ∀ i : Fin 200, Compatible (745600 + i.val) →
    (table.lookup (745600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3728 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 745600 745800 :=
  FiniteIntervals.of_fin 745600 200 complete_chunk3728

lemma complete_chunk3729 : ∀ i : Fin 200, Compatible (745800 + i.val) →
    (table.lookup (745800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3729 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 745800 746000 :=
  FiniteIntervals.of_fin 745800 200 complete_chunk3729

#print axioms interval_chunk3720
end Erdos184Work.PureFiveFilter4
