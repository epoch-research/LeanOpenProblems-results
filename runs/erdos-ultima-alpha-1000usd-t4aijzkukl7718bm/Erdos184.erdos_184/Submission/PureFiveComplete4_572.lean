import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5720 : ∀ i : Fin 200, Compatible (1144000 + i.val) →
    (table.lookup (1144000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5720 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1144000 1144200 :=
  FiniteIntervals.of_fin 1144000 200 complete_chunk5720

lemma complete_chunk5721 : ∀ i : Fin 200, Compatible (1144200 + i.val) →
    (table.lookup (1144200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5721 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1144200 1144400 :=
  FiniteIntervals.of_fin 1144200 200 complete_chunk5721

lemma complete_chunk5722 : ∀ i : Fin 200, Compatible (1144400 + i.val) →
    (table.lookup (1144400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5722 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1144400 1144600 :=
  FiniteIntervals.of_fin 1144400 200 complete_chunk5722

lemma complete_chunk5723 : ∀ i : Fin 200, Compatible (1144600 + i.val) →
    (table.lookup (1144600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5723 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1144600 1144800 :=
  FiniteIntervals.of_fin 1144600 200 complete_chunk5723

lemma complete_chunk5724 : ∀ i : Fin 200, Compatible (1144800 + i.val) →
    (table.lookup (1144800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5724 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1144800 1145000 :=
  FiniteIntervals.of_fin 1144800 200 complete_chunk5724

lemma complete_chunk5725 : ∀ i : Fin 200, Compatible (1145000 + i.val) →
    (table.lookup (1145000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5725 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1145000 1145200 :=
  FiniteIntervals.of_fin 1145000 200 complete_chunk5725

lemma complete_chunk5726 : ∀ i : Fin 200, Compatible (1145200 + i.val) →
    (table.lookup (1145200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5726 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1145200 1145400 :=
  FiniteIntervals.of_fin 1145200 200 complete_chunk5726

lemma complete_chunk5727 : ∀ i : Fin 200, Compatible (1145400 + i.val) →
    (table.lookup (1145400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5727 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1145400 1145600 :=
  FiniteIntervals.of_fin 1145400 200 complete_chunk5727

lemma complete_chunk5728 : ∀ i : Fin 200, Compatible (1145600 + i.val) →
    (table.lookup (1145600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5728 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1145600 1145800 :=
  FiniteIntervals.of_fin 1145600 200 complete_chunk5728

lemma complete_chunk5729 : ∀ i : Fin 200, Compatible (1145800 + i.val) →
    (table.lookup (1145800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5729 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1145800 1146000 :=
  FiniteIntervals.of_fin 1145800 200 complete_chunk5729

#print axioms interval_chunk5720
end Erdos184Work.PureFiveFilter4
