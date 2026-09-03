import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6110 : ∀ i : Fin 200, Compatible (1222000 + i.val) →
    (table.lookup (1222000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6110 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1222000 1222200 :=
  FiniteIntervals.of_fin 1222000 200 complete_chunk6110

lemma complete_chunk6111 : ∀ i : Fin 200, Compatible (1222200 + i.val) →
    (table.lookup (1222200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6111 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1222200 1222400 :=
  FiniteIntervals.of_fin 1222200 200 complete_chunk6111

lemma complete_chunk6112 : ∀ i : Fin 200, Compatible (1222400 + i.val) →
    (table.lookup (1222400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6112 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1222400 1222600 :=
  FiniteIntervals.of_fin 1222400 200 complete_chunk6112

lemma complete_chunk6113 : ∀ i : Fin 200, Compatible (1222600 + i.val) →
    (table.lookup (1222600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6113 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1222600 1222800 :=
  FiniteIntervals.of_fin 1222600 200 complete_chunk6113

lemma complete_chunk6114 : ∀ i : Fin 200, Compatible (1222800 + i.val) →
    (table.lookup (1222800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6114 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1222800 1223000 :=
  FiniteIntervals.of_fin 1222800 200 complete_chunk6114

lemma complete_chunk6115 : ∀ i : Fin 200, Compatible (1223000 + i.val) →
    (table.lookup (1223000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6115 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1223000 1223200 :=
  FiniteIntervals.of_fin 1223000 200 complete_chunk6115

lemma complete_chunk6116 : ∀ i : Fin 200, Compatible (1223200 + i.val) →
    (table.lookup (1223200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6116 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1223200 1223400 :=
  FiniteIntervals.of_fin 1223200 200 complete_chunk6116

lemma complete_chunk6117 : ∀ i : Fin 200, Compatible (1223400 + i.val) →
    (table.lookup (1223400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6117 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1223400 1223600 :=
  FiniteIntervals.of_fin 1223400 200 complete_chunk6117

lemma complete_chunk6118 : ∀ i : Fin 200, Compatible (1223600 + i.val) →
    (table.lookup (1223600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6118 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1223600 1223800 :=
  FiniteIntervals.of_fin 1223600 200 complete_chunk6118

lemma complete_chunk6119 : ∀ i : Fin 200, Compatible (1223800 + i.val) →
    (table.lookup (1223800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6119 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1223800 1224000 :=
  FiniteIntervals.of_fin 1223800 200 complete_chunk6119

#print axioms interval_chunk6110
end Erdos184Work.PureFiveFilter4
