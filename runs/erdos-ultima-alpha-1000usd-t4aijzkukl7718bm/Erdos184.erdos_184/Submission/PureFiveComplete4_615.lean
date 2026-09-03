import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6150 : ∀ i : Fin 200, Compatible (1230000 + i.val) →
    (table.lookup (1230000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6150 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1230000 1230200 :=
  FiniteIntervals.of_fin 1230000 200 complete_chunk6150

lemma complete_chunk6151 : ∀ i : Fin 200, Compatible (1230200 + i.val) →
    (table.lookup (1230200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6151 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1230200 1230400 :=
  FiniteIntervals.of_fin 1230200 200 complete_chunk6151

lemma complete_chunk6152 : ∀ i : Fin 200, Compatible (1230400 + i.val) →
    (table.lookup (1230400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6152 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1230400 1230600 :=
  FiniteIntervals.of_fin 1230400 200 complete_chunk6152

lemma complete_chunk6153 : ∀ i : Fin 200, Compatible (1230600 + i.val) →
    (table.lookup (1230600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6153 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1230600 1230800 :=
  FiniteIntervals.of_fin 1230600 200 complete_chunk6153

lemma complete_chunk6154 : ∀ i : Fin 200, Compatible (1230800 + i.val) →
    (table.lookup (1230800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6154 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1230800 1231000 :=
  FiniteIntervals.of_fin 1230800 200 complete_chunk6154

lemma complete_chunk6155 : ∀ i : Fin 200, Compatible (1231000 + i.val) →
    (table.lookup (1231000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6155 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1231000 1231200 :=
  FiniteIntervals.of_fin 1231000 200 complete_chunk6155

lemma complete_chunk6156 : ∀ i : Fin 200, Compatible (1231200 + i.val) →
    (table.lookup (1231200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6156 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1231200 1231400 :=
  FiniteIntervals.of_fin 1231200 200 complete_chunk6156

lemma complete_chunk6157 : ∀ i : Fin 200, Compatible (1231400 + i.val) →
    (table.lookup (1231400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6157 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1231400 1231600 :=
  FiniteIntervals.of_fin 1231400 200 complete_chunk6157

lemma complete_chunk6158 : ∀ i : Fin 200, Compatible (1231600 + i.val) →
    (table.lookup (1231600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6158 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1231600 1231800 :=
  FiniteIntervals.of_fin 1231600 200 complete_chunk6158

lemma complete_chunk6159 : ∀ i : Fin 200, Compatible (1231800 + i.val) →
    (table.lookup (1231800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6159 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1231800 1232000 :=
  FiniteIntervals.of_fin 1231800 200 complete_chunk6159

#print axioms interval_chunk6150
end Erdos184Work.PureFiveFilter4
