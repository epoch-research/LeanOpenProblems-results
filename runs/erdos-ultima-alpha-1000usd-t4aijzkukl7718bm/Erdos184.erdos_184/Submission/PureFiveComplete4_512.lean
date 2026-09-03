import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5120 : ∀ i : Fin 200, Compatible (1024000 + i.val) →
    (table.lookup (1024000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5120 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1024000 1024200 :=
  FiniteIntervals.of_fin 1024000 200 complete_chunk5120

lemma complete_chunk5121 : ∀ i : Fin 200, Compatible (1024200 + i.val) →
    (table.lookup (1024200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5121 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1024200 1024400 :=
  FiniteIntervals.of_fin 1024200 200 complete_chunk5121

lemma complete_chunk5122 : ∀ i : Fin 200, Compatible (1024400 + i.val) →
    (table.lookup (1024400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5122 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1024400 1024600 :=
  FiniteIntervals.of_fin 1024400 200 complete_chunk5122

lemma complete_chunk5123 : ∀ i : Fin 200, Compatible (1024600 + i.val) →
    (table.lookup (1024600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5123 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1024600 1024800 :=
  FiniteIntervals.of_fin 1024600 200 complete_chunk5123

lemma complete_chunk5124 : ∀ i : Fin 200, Compatible (1024800 + i.val) →
    (table.lookup (1024800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5124 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1024800 1025000 :=
  FiniteIntervals.of_fin 1024800 200 complete_chunk5124

lemma complete_chunk5125 : ∀ i : Fin 200, Compatible (1025000 + i.val) →
    (table.lookup (1025000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5125 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1025000 1025200 :=
  FiniteIntervals.of_fin 1025000 200 complete_chunk5125

lemma complete_chunk5126 : ∀ i : Fin 200, Compatible (1025200 + i.val) →
    (table.lookup (1025200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5126 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1025200 1025400 :=
  FiniteIntervals.of_fin 1025200 200 complete_chunk5126

lemma complete_chunk5127 : ∀ i : Fin 200, Compatible (1025400 + i.val) →
    (table.lookup (1025400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5127 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1025400 1025600 :=
  FiniteIntervals.of_fin 1025400 200 complete_chunk5127

lemma complete_chunk5128 : ∀ i : Fin 200, Compatible (1025600 + i.val) →
    (table.lookup (1025600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5128 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1025600 1025800 :=
  FiniteIntervals.of_fin 1025600 200 complete_chunk5128

lemma complete_chunk5129 : ∀ i : Fin 200, Compatible (1025800 + i.val) →
    (table.lookup (1025800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5129 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1025800 1026000 :=
  FiniteIntervals.of_fin 1025800 200 complete_chunk5129

#print axioms interval_chunk5120
end Erdos184Work.PureFiveFilter4
