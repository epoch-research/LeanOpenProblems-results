import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1040 : ∀ i : Fin 200, Compatible (208000 + i.val) →
    (table.lookup (208000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1040 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 208000 208200 :=
  FiniteIntervals.of_fin 208000 200 complete_chunk1040

lemma complete_chunk1041 : ∀ i : Fin 200, Compatible (208200 + i.val) →
    (table.lookup (208200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1041 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 208200 208400 :=
  FiniteIntervals.of_fin 208200 200 complete_chunk1041

lemma complete_chunk1042 : ∀ i : Fin 200, Compatible (208400 + i.val) →
    (table.lookup (208400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1042 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 208400 208600 :=
  FiniteIntervals.of_fin 208400 200 complete_chunk1042

lemma complete_chunk1043 : ∀ i : Fin 200, Compatible (208600 + i.val) →
    (table.lookup (208600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1043 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 208600 208800 :=
  FiniteIntervals.of_fin 208600 200 complete_chunk1043

lemma complete_chunk1044 : ∀ i : Fin 200, Compatible (208800 + i.val) →
    (table.lookup (208800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1044 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 208800 209000 :=
  FiniteIntervals.of_fin 208800 200 complete_chunk1044

lemma complete_chunk1045 : ∀ i : Fin 200, Compatible (209000 + i.val) →
    (table.lookup (209000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1045 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 209000 209200 :=
  FiniteIntervals.of_fin 209000 200 complete_chunk1045

lemma complete_chunk1046 : ∀ i : Fin 200, Compatible (209200 + i.val) →
    (table.lookup (209200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1046 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 209200 209400 :=
  FiniteIntervals.of_fin 209200 200 complete_chunk1046

lemma complete_chunk1047 : ∀ i : Fin 200, Compatible (209400 + i.val) →
    (table.lookup (209400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1047 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 209400 209600 :=
  FiniteIntervals.of_fin 209400 200 complete_chunk1047

lemma complete_chunk1048 : ∀ i : Fin 200, Compatible (209600 + i.val) →
    (table.lookup (209600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1048 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 209600 209800 :=
  FiniteIntervals.of_fin 209600 200 complete_chunk1048

lemma complete_chunk1049 : ∀ i : Fin 200, Compatible (209800 + i.val) →
    (table.lookup (209800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1049 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 209800 210000 :=
  FiniteIntervals.of_fin 209800 200 complete_chunk1049

#print axioms interval_chunk1040
end Erdos184Work.PureFiveFilter4
