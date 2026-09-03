import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5180 : ∀ i : Fin 200, Compatible (1036000 + i.val) →
    (table.lookup (1036000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5180 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1036000 1036200 :=
  FiniteIntervals.of_fin 1036000 200 complete_chunk5180

lemma complete_chunk5181 : ∀ i : Fin 200, Compatible (1036200 + i.val) →
    (table.lookup (1036200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5181 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1036200 1036400 :=
  FiniteIntervals.of_fin 1036200 200 complete_chunk5181

lemma complete_chunk5182 : ∀ i : Fin 200, Compatible (1036400 + i.val) →
    (table.lookup (1036400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5182 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1036400 1036600 :=
  FiniteIntervals.of_fin 1036400 200 complete_chunk5182

lemma complete_chunk5183 : ∀ i : Fin 200, Compatible (1036600 + i.val) →
    (table.lookup (1036600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5183 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1036600 1036800 :=
  FiniteIntervals.of_fin 1036600 200 complete_chunk5183

lemma complete_chunk5184 : ∀ i : Fin 200, Compatible (1036800 + i.val) →
    (table.lookup (1036800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5184 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1036800 1037000 :=
  FiniteIntervals.of_fin 1036800 200 complete_chunk5184

lemma complete_chunk5185 : ∀ i : Fin 200, Compatible (1037000 + i.val) →
    (table.lookup (1037000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5185 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1037000 1037200 :=
  FiniteIntervals.of_fin 1037000 200 complete_chunk5185

lemma complete_chunk5186 : ∀ i : Fin 200, Compatible (1037200 + i.val) →
    (table.lookup (1037200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5186 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1037200 1037400 :=
  FiniteIntervals.of_fin 1037200 200 complete_chunk5186

lemma complete_chunk5187 : ∀ i : Fin 200, Compatible (1037400 + i.val) →
    (table.lookup (1037400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5187 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1037400 1037600 :=
  FiniteIntervals.of_fin 1037400 200 complete_chunk5187

lemma complete_chunk5188 : ∀ i : Fin 200, Compatible (1037600 + i.val) →
    (table.lookup (1037600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5188 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1037600 1037800 :=
  FiniteIntervals.of_fin 1037600 200 complete_chunk5188

lemma complete_chunk5189 : ∀ i : Fin 200, Compatible (1037800 + i.val) →
    (table.lookup (1037800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5189 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1037800 1038000 :=
  FiniteIntervals.of_fin 1037800 200 complete_chunk5189

#print axioms interval_chunk5180
end Erdos184Work.PureFiveFilter4
