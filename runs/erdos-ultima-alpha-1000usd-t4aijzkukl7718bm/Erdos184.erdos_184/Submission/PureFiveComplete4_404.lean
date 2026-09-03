import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4040 : ∀ i : Fin 200, Compatible (808000 + i.val) →
    (table.lookup (808000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4040 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 808000 808200 :=
  FiniteIntervals.of_fin 808000 200 complete_chunk4040

lemma complete_chunk4041 : ∀ i : Fin 200, Compatible (808200 + i.val) →
    (table.lookup (808200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4041 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 808200 808400 :=
  FiniteIntervals.of_fin 808200 200 complete_chunk4041

lemma complete_chunk4042 : ∀ i : Fin 200, Compatible (808400 + i.val) →
    (table.lookup (808400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4042 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 808400 808600 :=
  FiniteIntervals.of_fin 808400 200 complete_chunk4042

lemma complete_chunk4043 : ∀ i : Fin 200, Compatible (808600 + i.val) →
    (table.lookup (808600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4043 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 808600 808800 :=
  FiniteIntervals.of_fin 808600 200 complete_chunk4043

lemma complete_chunk4044 : ∀ i : Fin 200, Compatible (808800 + i.val) →
    (table.lookup (808800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4044 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 808800 809000 :=
  FiniteIntervals.of_fin 808800 200 complete_chunk4044

lemma complete_chunk4045 : ∀ i : Fin 200, Compatible (809000 + i.val) →
    (table.lookup (809000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4045 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 809000 809200 :=
  FiniteIntervals.of_fin 809000 200 complete_chunk4045

lemma complete_chunk4046 : ∀ i : Fin 200, Compatible (809200 + i.val) →
    (table.lookup (809200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4046 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 809200 809400 :=
  FiniteIntervals.of_fin 809200 200 complete_chunk4046

lemma complete_chunk4047 : ∀ i : Fin 200, Compatible (809400 + i.val) →
    (table.lookup (809400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4047 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 809400 809600 :=
  FiniteIntervals.of_fin 809400 200 complete_chunk4047

lemma complete_chunk4048 : ∀ i : Fin 200, Compatible (809600 + i.val) →
    (table.lookup (809600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4048 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 809600 809800 :=
  FiniteIntervals.of_fin 809600 200 complete_chunk4048

lemma complete_chunk4049 : ∀ i : Fin 200, Compatible (809800 + i.val) →
    (table.lookup (809800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4049 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 809800 810000 :=
  FiniteIntervals.of_fin 809800 200 complete_chunk4049

#print axioms interval_chunk4040
end Erdos184Work.PureFiveFilter4
