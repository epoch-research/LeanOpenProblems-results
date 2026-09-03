import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4120 : ∀ i : Fin 200, Compatible (824000 + i.val) →
    (table.lookup (824000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4120 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 824000 824200 :=
  FiniteIntervals.of_fin 824000 200 complete_chunk4120

lemma complete_chunk4121 : ∀ i : Fin 200, Compatible (824200 + i.val) →
    (table.lookup (824200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4121 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 824200 824400 :=
  FiniteIntervals.of_fin 824200 200 complete_chunk4121

lemma complete_chunk4122 : ∀ i : Fin 200, Compatible (824400 + i.val) →
    (table.lookup (824400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4122 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 824400 824600 :=
  FiniteIntervals.of_fin 824400 200 complete_chunk4122

lemma complete_chunk4123 : ∀ i : Fin 200, Compatible (824600 + i.val) →
    (table.lookup (824600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4123 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 824600 824800 :=
  FiniteIntervals.of_fin 824600 200 complete_chunk4123

lemma complete_chunk4124 : ∀ i : Fin 200, Compatible (824800 + i.val) →
    (table.lookup (824800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4124 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 824800 825000 :=
  FiniteIntervals.of_fin 824800 200 complete_chunk4124

lemma complete_chunk4125 : ∀ i : Fin 200, Compatible (825000 + i.val) →
    (table.lookup (825000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4125 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 825000 825200 :=
  FiniteIntervals.of_fin 825000 200 complete_chunk4125

lemma complete_chunk4126 : ∀ i : Fin 200, Compatible (825200 + i.val) →
    (table.lookup (825200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4126 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 825200 825400 :=
  FiniteIntervals.of_fin 825200 200 complete_chunk4126

lemma complete_chunk4127 : ∀ i : Fin 200, Compatible (825400 + i.val) →
    (table.lookup (825400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4127 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 825400 825600 :=
  FiniteIntervals.of_fin 825400 200 complete_chunk4127

lemma complete_chunk4128 : ∀ i : Fin 200, Compatible (825600 + i.val) →
    (table.lookup (825600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4128 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 825600 825800 :=
  FiniteIntervals.of_fin 825600 200 complete_chunk4128

lemma complete_chunk4129 : ∀ i : Fin 200, Compatible (825800 + i.val) →
    (table.lookup (825800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4129 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 825800 826000 :=
  FiniteIntervals.of_fin 825800 200 complete_chunk4129

#print axioms interval_chunk4120
end Erdos184Work.PureFiveFilter4
