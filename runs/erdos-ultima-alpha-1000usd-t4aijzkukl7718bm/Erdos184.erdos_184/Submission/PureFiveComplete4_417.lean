import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4170 : ∀ i : Fin 200, Compatible (834000 + i.val) →
    (table.lookup (834000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4170 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 834000 834200 :=
  FiniteIntervals.of_fin 834000 200 complete_chunk4170

lemma complete_chunk4171 : ∀ i : Fin 200, Compatible (834200 + i.val) →
    (table.lookup (834200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4171 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 834200 834400 :=
  FiniteIntervals.of_fin 834200 200 complete_chunk4171

lemma complete_chunk4172 : ∀ i : Fin 200, Compatible (834400 + i.val) →
    (table.lookup (834400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4172 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 834400 834600 :=
  FiniteIntervals.of_fin 834400 200 complete_chunk4172

lemma complete_chunk4173 : ∀ i : Fin 200, Compatible (834600 + i.val) →
    (table.lookup (834600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4173 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 834600 834800 :=
  FiniteIntervals.of_fin 834600 200 complete_chunk4173

lemma complete_chunk4174 : ∀ i : Fin 200, Compatible (834800 + i.val) →
    (table.lookup (834800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4174 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 834800 835000 :=
  FiniteIntervals.of_fin 834800 200 complete_chunk4174

lemma complete_chunk4175 : ∀ i : Fin 200, Compatible (835000 + i.val) →
    (table.lookup (835000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4175 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 835000 835200 :=
  FiniteIntervals.of_fin 835000 200 complete_chunk4175

lemma complete_chunk4176 : ∀ i : Fin 200, Compatible (835200 + i.val) →
    (table.lookup (835200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4176 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 835200 835400 :=
  FiniteIntervals.of_fin 835200 200 complete_chunk4176

lemma complete_chunk4177 : ∀ i : Fin 200, Compatible (835400 + i.val) →
    (table.lookup (835400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4177 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 835400 835600 :=
  FiniteIntervals.of_fin 835400 200 complete_chunk4177

lemma complete_chunk4178 : ∀ i : Fin 200, Compatible (835600 + i.val) →
    (table.lookup (835600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4178 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 835600 835800 :=
  FiniteIntervals.of_fin 835600 200 complete_chunk4178

lemma complete_chunk4179 : ∀ i : Fin 200, Compatible (835800 + i.val) →
    (table.lookup (835800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4179 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 835800 836000 :=
  FiniteIntervals.of_fin 835800 200 complete_chunk4179

#print axioms interval_chunk4170
end Erdos184Work.PureFiveFilter4
