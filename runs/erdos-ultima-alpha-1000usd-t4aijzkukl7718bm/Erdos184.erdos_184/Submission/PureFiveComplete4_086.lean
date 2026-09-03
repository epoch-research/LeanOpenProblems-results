import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk860 : ∀ i : Fin 200, Compatible (172000 + i.val) →
    (table.lookup (172000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk860 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 172000 172200 :=
  FiniteIntervals.of_fin 172000 200 complete_chunk860

lemma complete_chunk861 : ∀ i : Fin 200, Compatible (172200 + i.val) →
    (table.lookup (172200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk861 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 172200 172400 :=
  FiniteIntervals.of_fin 172200 200 complete_chunk861

lemma complete_chunk862 : ∀ i : Fin 200, Compatible (172400 + i.val) →
    (table.lookup (172400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk862 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 172400 172600 :=
  FiniteIntervals.of_fin 172400 200 complete_chunk862

lemma complete_chunk863 : ∀ i : Fin 200, Compatible (172600 + i.val) →
    (table.lookup (172600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk863 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 172600 172800 :=
  FiniteIntervals.of_fin 172600 200 complete_chunk863

lemma complete_chunk864 : ∀ i : Fin 200, Compatible (172800 + i.val) →
    (table.lookup (172800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk864 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 172800 173000 :=
  FiniteIntervals.of_fin 172800 200 complete_chunk864

lemma complete_chunk865 : ∀ i : Fin 200, Compatible (173000 + i.val) →
    (table.lookup (173000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk865 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 173000 173200 :=
  FiniteIntervals.of_fin 173000 200 complete_chunk865

lemma complete_chunk866 : ∀ i : Fin 200, Compatible (173200 + i.val) →
    (table.lookup (173200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk866 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 173200 173400 :=
  FiniteIntervals.of_fin 173200 200 complete_chunk866

lemma complete_chunk867 : ∀ i : Fin 200, Compatible (173400 + i.val) →
    (table.lookup (173400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk867 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 173400 173600 :=
  FiniteIntervals.of_fin 173400 200 complete_chunk867

lemma complete_chunk868 : ∀ i : Fin 200, Compatible (173600 + i.val) →
    (table.lookup (173600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk868 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 173600 173800 :=
  FiniteIntervals.of_fin 173600 200 complete_chunk868

lemma complete_chunk869 : ∀ i : Fin 200, Compatible (173800 + i.val) →
    (table.lookup (173800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk869 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 173800 174000 :=
  FiniteIntervals.of_fin 173800 200 complete_chunk869

#print axioms interval_chunk860
end Erdos184Work.PureFiveFilter4
