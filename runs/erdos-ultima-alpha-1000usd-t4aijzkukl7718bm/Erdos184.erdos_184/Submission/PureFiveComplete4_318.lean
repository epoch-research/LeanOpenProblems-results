import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3180 : ∀ i : Fin 200, Compatible (636000 + i.val) →
    (table.lookup (636000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3180 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 636000 636200 :=
  FiniteIntervals.of_fin 636000 200 complete_chunk3180

lemma complete_chunk3181 : ∀ i : Fin 200, Compatible (636200 + i.val) →
    (table.lookup (636200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3181 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 636200 636400 :=
  FiniteIntervals.of_fin 636200 200 complete_chunk3181

lemma complete_chunk3182 : ∀ i : Fin 200, Compatible (636400 + i.val) →
    (table.lookup (636400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3182 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 636400 636600 :=
  FiniteIntervals.of_fin 636400 200 complete_chunk3182

lemma complete_chunk3183 : ∀ i : Fin 200, Compatible (636600 + i.val) →
    (table.lookup (636600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3183 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 636600 636800 :=
  FiniteIntervals.of_fin 636600 200 complete_chunk3183

lemma complete_chunk3184 : ∀ i : Fin 200, Compatible (636800 + i.val) →
    (table.lookup (636800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3184 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 636800 637000 :=
  FiniteIntervals.of_fin 636800 200 complete_chunk3184

lemma complete_chunk3185 : ∀ i : Fin 200, Compatible (637000 + i.val) →
    (table.lookup (637000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3185 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 637000 637200 :=
  FiniteIntervals.of_fin 637000 200 complete_chunk3185

lemma complete_chunk3186 : ∀ i : Fin 200, Compatible (637200 + i.val) →
    (table.lookup (637200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3186 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 637200 637400 :=
  FiniteIntervals.of_fin 637200 200 complete_chunk3186

lemma complete_chunk3187 : ∀ i : Fin 200, Compatible (637400 + i.val) →
    (table.lookup (637400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3187 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 637400 637600 :=
  FiniteIntervals.of_fin 637400 200 complete_chunk3187

lemma complete_chunk3188 : ∀ i : Fin 200, Compatible (637600 + i.val) →
    (table.lookup (637600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3188 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 637600 637800 :=
  FiniteIntervals.of_fin 637600 200 complete_chunk3188

lemma complete_chunk3189 : ∀ i : Fin 200, Compatible (637800 + i.val) →
    (table.lookup (637800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3189 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 637800 638000 :=
  FiniteIntervals.of_fin 637800 200 complete_chunk3189

#print axioms interval_chunk3180
end Erdos184Work.PureFiveFilter4
