import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1110 : ∀ i : Fin 200, Compatible (222000 + i.val) →
    (table.lookup (222000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1110 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 222000 222200 :=
  FiniteIntervals.of_fin 222000 200 complete_chunk1110

lemma complete_chunk1111 : ∀ i : Fin 200, Compatible (222200 + i.val) →
    (table.lookup (222200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1111 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 222200 222400 :=
  FiniteIntervals.of_fin 222200 200 complete_chunk1111

lemma complete_chunk1112 : ∀ i : Fin 200, Compatible (222400 + i.val) →
    (table.lookup (222400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1112 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 222400 222600 :=
  FiniteIntervals.of_fin 222400 200 complete_chunk1112

lemma complete_chunk1113 : ∀ i : Fin 200, Compatible (222600 + i.val) →
    (table.lookup (222600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1113 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 222600 222800 :=
  FiniteIntervals.of_fin 222600 200 complete_chunk1113

lemma complete_chunk1114 : ∀ i : Fin 200, Compatible (222800 + i.val) →
    (table.lookup (222800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1114 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 222800 223000 :=
  FiniteIntervals.of_fin 222800 200 complete_chunk1114

lemma complete_chunk1115 : ∀ i : Fin 200, Compatible (223000 + i.val) →
    (table.lookup (223000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1115 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 223000 223200 :=
  FiniteIntervals.of_fin 223000 200 complete_chunk1115

lemma complete_chunk1116 : ∀ i : Fin 200, Compatible (223200 + i.val) →
    (table.lookup (223200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1116 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 223200 223400 :=
  FiniteIntervals.of_fin 223200 200 complete_chunk1116

lemma complete_chunk1117 : ∀ i : Fin 200, Compatible (223400 + i.val) →
    (table.lookup (223400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1117 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 223400 223600 :=
  FiniteIntervals.of_fin 223400 200 complete_chunk1117

lemma complete_chunk1118 : ∀ i : Fin 200, Compatible (223600 + i.val) →
    (table.lookup (223600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1118 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 223600 223800 :=
  FiniteIntervals.of_fin 223600 200 complete_chunk1118

lemma complete_chunk1119 : ∀ i : Fin 200, Compatible (223800 + i.val) →
    (table.lookup (223800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1119 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 223800 224000 :=
  FiniteIntervals.of_fin 223800 200 complete_chunk1119

#print axioms interval_chunk1110
end Erdos184Work.PureFiveFilter4
