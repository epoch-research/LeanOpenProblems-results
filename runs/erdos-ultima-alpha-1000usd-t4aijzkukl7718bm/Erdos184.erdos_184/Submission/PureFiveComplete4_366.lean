import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3660 : ∀ i : Fin 200, Compatible (732000 + i.val) →
    (table.lookup (732000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3660 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 732000 732200 :=
  FiniteIntervals.of_fin 732000 200 complete_chunk3660

lemma complete_chunk3661 : ∀ i : Fin 200, Compatible (732200 + i.val) →
    (table.lookup (732200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3661 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 732200 732400 :=
  FiniteIntervals.of_fin 732200 200 complete_chunk3661

lemma complete_chunk3662 : ∀ i : Fin 200, Compatible (732400 + i.val) →
    (table.lookup (732400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3662 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 732400 732600 :=
  FiniteIntervals.of_fin 732400 200 complete_chunk3662

lemma complete_chunk3663 : ∀ i : Fin 200, Compatible (732600 + i.val) →
    (table.lookup (732600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3663 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 732600 732800 :=
  FiniteIntervals.of_fin 732600 200 complete_chunk3663

lemma complete_chunk3664 : ∀ i : Fin 200, Compatible (732800 + i.val) →
    (table.lookup (732800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3664 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 732800 733000 :=
  FiniteIntervals.of_fin 732800 200 complete_chunk3664

lemma complete_chunk3665 : ∀ i : Fin 200, Compatible (733000 + i.val) →
    (table.lookup (733000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3665 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 733000 733200 :=
  FiniteIntervals.of_fin 733000 200 complete_chunk3665

lemma complete_chunk3666 : ∀ i : Fin 200, Compatible (733200 + i.val) →
    (table.lookup (733200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3666 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 733200 733400 :=
  FiniteIntervals.of_fin 733200 200 complete_chunk3666

lemma complete_chunk3667 : ∀ i : Fin 200, Compatible (733400 + i.val) →
    (table.lookup (733400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3667 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 733400 733600 :=
  FiniteIntervals.of_fin 733400 200 complete_chunk3667

lemma complete_chunk3668 : ∀ i : Fin 200, Compatible (733600 + i.val) →
    (table.lookup (733600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3668 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 733600 733800 :=
  FiniteIntervals.of_fin 733600 200 complete_chunk3668

lemma complete_chunk3669 : ∀ i : Fin 200, Compatible (733800 + i.val) →
    (table.lookup (733800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3669 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 733800 734000 :=
  FiniteIntervals.of_fin 733800 200 complete_chunk3669

#print axioms interval_chunk3660
end Erdos184Work.PureFiveFilter4
