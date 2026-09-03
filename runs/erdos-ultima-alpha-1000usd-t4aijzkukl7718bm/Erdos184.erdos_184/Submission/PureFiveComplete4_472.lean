import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4720 : ∀ i : Fin 200, Compatible (944000 + i.val) →
    (table.lookup (944000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4720 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 944000 944200 :=
  FiniteIntervals.of_fin 944000 200 complete_chunk4720

lemma complete_chunk4721 : ∀ i : Fin 200, Compatible (944200 + i.val) →
    (table.lookup (944200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4721 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 944200 944400 :=
  FiniteIntervals.of_fin 944200 200 complete_chunk4721

lemma complete_chunk4722 : ∀ i : Fin 200, Compatible (944400 + i.val) →
    (table.lookup (944400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4722 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 944400 944600 :=
  FiniteIntervals.of_fin 944400 200 complete_chunk4722

lemma complete_chunk4723 : ∀ i : Fin 200, Compatible (944600 + i.val) →
    (table.lookup (944600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4723 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 944600 944800 :=
  FiniteIntervals.of_fin 944600 200 complete_chunk4723

lemma complete_chunk4724 : ∀ i : Fin 200, Compatible (944800 + i.val) →
    (table.lookup (944800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4724 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 944800 945000 :=
  FiniteIntervals.of_fin 944800 200 complete_chunk4724

lemma complete_chunk4725 : ∀ i : Fin 200, Compatible (945000 + i.val) →
    (table.lookup (945000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4725 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 945000 945200 :=
  FiniteIntervals.of_fin 945000 200 complete_chunk4725

lemma complete_chunk4726 : ∀ i : Fin 200, Compatible (945200 + i.val) →
    (table.lookup (945200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4726 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 945200 945400 :=
  FiniteIntervals.of_fin 945200 200 complete_chunk4726

lemma complete_chunk4727 : ∀ i : Fin 200, Compatible (945400 + i.val) →
    (table.lookup (945400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4727 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 945400 945600 :=
  FiniteIntervals.of_fin 945400 200 complete_chunk4727

lemma complete_chunk4728 : ∀ i : Fin 200, Compatible (945600 + i.val) →
    (table.lookup (945600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4728 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 945600 945800 :=
  FiniteIntervals.of_fin 945600 200 complete_chunk4728

lemma complete_chunk4729 : ∀ i : Fin 200, Compatible (945800 + i.val) →
    (table.lookup (945800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4729 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 945800 946000 :=
  FiniteIntervals.of_fin 945800 200 complete_chunk4729

#print axioms interval_chunk4720
end Erdos184Work.PureFiveFilter4
