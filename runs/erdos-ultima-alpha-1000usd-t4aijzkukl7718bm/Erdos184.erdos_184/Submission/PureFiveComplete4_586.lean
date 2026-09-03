import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5860 : ∀ i : Fin 200, Compatible (1172000 + i.val) →
    (table.lookup (1172000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5860 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1172000 1172200 :=
  FiniteIntervals.of_fin 1172000 200 complete_chunk5860

lemma complete_chunk5861 : ∀ i : Fin 200, Compatible (1172200 + i.val) →
    (table.lookup (1172200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5861 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1172200 1172400 :=
  FiniteIntervals.of_fin 1172200 200 complete_chunk5861

lemma complete_chunk5862 : ∀ i : Fin 200, Compatible (1172400 + i.val) →
    (table.lookup (1172400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5862 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1172400 1172600 :=
  FiniteIntervals.of_fin 1172400 200 complete_chunk5862

lemma complete_chunk5863 : ∀ i : Fin 200, Compatible (1172600 + i.val) →
    (table.lookup (1172600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5863 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1172600 1172800 :=
  FiniteIntervals.of_fin 1172600 200 complete_chunk5863

lemma complete_chunk5864 : ∀ i : Fin 200, Compatible (1172800 + i.val) →
    (table.lookup (1172800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5864 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1172800 1173000 :=
  FiniteIntervals.of_fin 1172800 200 complete_chunk5864

lemma complete_chunk5865 : ∀ i : Fin 200, Compatible (1173000 + i.val) →
    (table.lookup (1173000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5865 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1173000 1173200 :=
  FiniteIntervals.of_fin 1173000 200 complete_chunk5865

lemma complete_chunk5866 : ∀ i : Fin 200, Compatible (1173200 + i.val) →
    (table.lookup (1173200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5866 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1173200 1173400 :=
  FiniteIntervals.of_fin 1173200 200 complete_chunk5866

lemma complete_chunk5867 : ∀ i : Fin 200, Compatible (1173400 + i.val) →
    (table.lookup (1173400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5867 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1173400 1173600 :=
  FiniteIntervals.of_fin 1173400 200 complete_chunk5867

lemma complete_chunk5868 : ∀ i : Fin 200, Compatible (1173600 + i.val) →
    (table.lookup (1173600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5868 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1173600 1173800 :=
  FiniteIntervals.of_fin 1173600 200 complete_chunk5868

lemma complete_chunk5869 : ∀ i : Fin 200, Compatible (1173800 + i.val) →
    (table.lookup (1173800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5869 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1173800 1174000 :=
  FiniteIntervals.of_fin 1173800 200 complete_chunk5869

#print axioms interval_chunk5860
end Erdos184Work.PureFiveFilter4
