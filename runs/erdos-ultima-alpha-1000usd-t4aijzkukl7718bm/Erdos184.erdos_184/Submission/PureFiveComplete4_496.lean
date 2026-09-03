import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4960 : ∀ i : Fin 200, Compatible (992000 + i.val) →
    (table.lookup (992000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4960 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 992000 992200 :=
  FiniteIntervals.of_fin 992000 200 complete_chunk4960

lemma complete_chunk4961 : ∀ i : Fin 200, Compatible (992200 + i.val) →
    (table.lookup (992200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4961 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 992200 992400 :=
  FiniteIntervals.of_fin 992200 200 complete_chunk4961

lemma complete_chunk4962 : ∀ i : Fin 200, Compatible (992400 + i.val) →
    (table.lookup (992400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4962 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 992400 992600 :=
  FiniteIntervals.of_fin 992400 200 complete_chunk4962

lemma complete_chunk4963 : ∀ i : Fin 200, Compatible (992600 + i.val) →
    (table.lookup (992600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4963 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 992600 992800 :=
  FiniteIntervals.of_fin 992600 200 complete_chunk4963

lemma complete_chunk4964 : ∀ i : Fin 200, Compatible (992800 + i.val) →
    (table.lookup (992800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4964 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 992800 993000 :=
  FiniteIntervals.of_fin 992800 200 complete_chunk4964

lemma complete_chunk4965 : ∀ i : Fin 200, Compatible (993000 + i.val) →
    (table.lookup (993000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4965 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 993000 993200 :=
  FiniteIntervals.of_fin 993000 200 complete_chunk4965

lemma complete_chunk4966 : ∀ i : Fin 200, Compatible (993200 + i.val) →
    (table.lookup (993200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4966 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 993200 993400 :=
  FiniteIntervals.of_fin 993200 200 complete_chunk4966

lemma complete_chunk4967 : ∀ i : Fin 200, Compatible (993400 + i.val) →
    (table.lookup (993400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4967 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 993400 993600 :=
  FiniteIntervals.of_fin 993400 200 complete_chunk4967

lemma complete_chunk4968 : ∀ i : Fin 200, Compatible (993600 + i.val) →
    (table.lookup (993600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4968 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 993600 993800 :=
  FiniteIntervals.of_fin 993600 200 complete_chunk4968

lemma complete_chunk4969 : ∀ i : Fin 200, Compatible (993800 + i.val) →
    (table.lookup (993800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4969 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 993800 994000 :=
  FiniteIntervals.of_fin 993800 200 complete_chunk4969

#print axioms interval_chunk4960
end Erdos184Work.PureFiveFilter4
