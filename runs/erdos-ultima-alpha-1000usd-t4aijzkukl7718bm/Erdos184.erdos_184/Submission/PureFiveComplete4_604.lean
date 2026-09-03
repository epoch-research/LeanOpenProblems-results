import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6040 : ∀ i : Fin 200, Compatible (1208000 + i.val) →
    (table.lookup (1208000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6040 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1208000 1208200 :=
  FiniteIntervals.of_fin 1208000 200 complete_chunk6040

lemma complete_chunk6041 : ∀ i : Fin 200, Compatible (1208200 + i.val) →
    (table.lookup (1208200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6041 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1208200 1208400 :=
  FiniteIntervals.of_fin 1208200 200 complete_chunk6041

lemma complete_chunk6042 : ∀ i : Fin 200, Compatible (1208400 + i.val) →
    (table.lookup (1208400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6042 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1208400 1208600 :=
  FiniteIntervals.of_fin 1208400 200 complete_chunk6042

lemma complete_chunk6043 : ∀ i : Fin 200, Compatible (1208600 + i.val) →
    (table.lookup (1208600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6043 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1208600 1208800 :=
  FiniteIntervals.of_fin 1208600 200 complete_chunk6043

lemma complete_chunk6044 : ∀ i : Fin 200, Compatible (1208800 + i.val) →
    (table.lookup (1208800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6044 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1208800 1209000 :=
  FiniteIntervals.of_fin 1208800 200 complete_chunk6044

lemma complete_chunk6045 : ∀ i : Fin 200, Compatible (1209000 + i.val) →
    (table.lookup (1209000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6045 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1209000 1209200 :=
  FiniteIntervals.of_fin 1209000 200 complete_chunk6045

lemma complete_chunk6046 : ∀ i : Fin 200, Compatible (1209200 + i.val) →
    (table.lookup (1209200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6046 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1209200 1209400 :=
  FiniteIntervals.of_fin 1209200 200 complete_chunk6046

lemma complete_chunk6047 : ∀ i : Fin 200, Compatible (1209400 + i.val) →
    (table.lookup (1209400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6047 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1209400 1209600 :=
  FiniteIntervals.of_fin 1209400 200 complete_chunk6047

lemma complete_chunk6048 : ∀ i : Fin 200, Compatible (1209600 + i.val) →
    (table.lookup (1209600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6048 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1209600 1209800 :=
  FiniteIntervals.of_fin 1209600 200 complete_chunk6048

lemma complete_chunk6049 : ∀ i : Fin 200, Compatible (1209800 + i.val) →
    (table.lookup (1209800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6049 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1209800 1210000 :=
  FiniteIntervals.of_fin 1209800 200 complete_chunk6049

#print axioms interval_chunk6040
end Erdos184Work.PureFiveFilter4
