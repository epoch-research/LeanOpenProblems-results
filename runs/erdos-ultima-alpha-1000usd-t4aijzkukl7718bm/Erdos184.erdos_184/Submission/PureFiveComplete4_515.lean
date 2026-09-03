import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5150 : ∀ i : Fin 200, Compatible (1030000 + i.val) →
    (table.lookup (1030000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5150 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1030000 1030200 :=
  FiniteIntervals.of_fin 1030000 200 complete_chunk5150

lemma complete_chunk5151 : ∀ i : Fin 200, Compatible (1030200 + i.val) →
    (table.lookup (1030200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5151 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1030200 1030400 :=
  FiniteIntervals.of_fin 1030200 200 complete_chunk5151

lemma complete_chunk5152 : ∀ i : Fin 200, Compatible (1030400 + i.val) →
    (table.lookup (1030400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5152 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1030400 1030600 :=
  FiniteIntervals.of_fin 1030400 200 complete_chunk5152

lemma complete_chunk5153 : ∀ i : Fin 200, Compatible (1030600 + i.val) →
    (table.lookup (1030600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5153 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1030600 1030800 :=
  FiniteIntervals.of_fin 1030600 200 complete_chunk5153

lemma complete_chunk5154 : ∀ i : Fin 200, Compatible (1030800 + i.val) →
    (table.lookup (1030800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5154 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1030800 1031000 :=
  FiniteIntervals.of_fin 1030800 200 complete_chunk5154

lemma complete_chunk5155 : ∀ i : Fin 200, Compatible (1031000 + i.val) →
    (table.lookup (1031000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5155 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1031000 1031200 :=
  FiniteIntervals.of_fin 1031000 200 complete_chunk5155

lemma complete_chunk5156 : ∀ i : Fin 200, Compatible (1031200 + i.val) →
    (table.lookup (1031200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5156 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1031200 1031400 :=
  FiniteIntervals.of_fin 1031200 200 complete_chunk5156

lemma complete_chunk5157 : ∀ i : Fin 200, Compatible (1031400 + i.val) →
    (table.lookup (1031400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5157 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1031400 1031600 :=
  FiniteIntervals.of_fin 1031400 200 complete_chunk5157

lemma complete_chunk5158 : ∀ i : Fin 200, Compatible (1031600 + i.val) →
    (table.lookup (1031600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5158 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1031600 1031800 :=
  FiniteIntervals.of_fin 1031600 200 complete_chunk5158

lemma complete_chunk5159 : ∀ i : Fin 200, Compatible (1031800 + i.val) →
    (table.lookup (1031800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5159 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1031800 1032000 :=
  FiniteIntervals.of_fin 1031800 200 complete_chunk5159

#print axioms interval_chunk5150
end Erdos184Work.PureFiveFilter4
