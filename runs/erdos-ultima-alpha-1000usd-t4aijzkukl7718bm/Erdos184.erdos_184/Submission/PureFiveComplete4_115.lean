import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1150 : ∀ i : Fin 200, Compatible (230000 + i.val) →
    (table.lookup (230000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1150 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 230000 230200 :=
  FiniteIntervals.of_fin 230000 200 complete_chunk1150

lemma complete_chunk1151 : ∀ i : Fin 200, Compatible (230200 + i.val) →
    (table.lookup (230200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1151 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 230200 230400 :=
  FiniteIntervals.of_fin 230200 200 complete_chunk1151

lemma complete_chunk1152 : ∀ i : Fin 200, Compatible (230400 + i.val) →
    (table.lookup (230400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1152 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 230400 230600 :=
  FiniteIntervals.of_fin 230400 200 complete_chunk1152

lemma complete_chunk1153 : ∀ i : Fin 200, Compatible (230600 + i.val) →
    (table.lookup (230600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1153 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 230600 230800 :=
  FiniteIntervals.of_fin 230600 200 complete_chunk1153

lemma complete_chunk1154 : ∀ i : Fin 200, Compatible (230800 + i.val) →
    (table.lookup (230800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1154 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 230800 231000 :=
  FiniteIntervals.of_fin 230800 200 complete_chunk1154

lemma complete_chunk1155 : ∀ i : Fin 200, Compatible (231000 + i.val) →
    (table.lookup (231000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1155 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 231000 231200 :=
  FiniteIntervals.of_fin 231000 200 complete_chunk1155

lemma complete_chunk1156 : ∀ i : Fin 200, Compatible (231200 + i.val) →
    (table.lookup (231200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1156 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 231200 231400 :=
  FiniteIntervals.of_fin 231200 200 complete_chunk1156

lemma complete_chunk1157 : ∀ i : Fin 200, Compatible (231400 + i.val) →
    (table.lookup (231400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1157 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 231400 231600 :=
  FiniteIntervals.of_fin 231400 200 complete_chunk1157

lemma complete_chunk1158 : ∀ i : Fin 200, Compatible (231600 + i.val) →
    (table.lookup (231600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1158 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 231600 231800 :=
  FiniteIntervals.of_fin 231600 200 complete_chunk1158

lemma complete_chunk1159 : ∀ i : Fin 200, Compatible (231800 + i.val) →
    (table.lookup (231800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1159 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 231800 232000 :=
  FiniteIntervals.of_fin 231800 200 complete_chunk1159

#print axioms interval_chunk1150
end Erdos184Work.PureFiveFilter4
