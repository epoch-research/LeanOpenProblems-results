import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3170 : ∀ i : Fin 200, Compatible (634000 + i.val) →
    (table.lookup (634000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3170 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 634000 634200 :=
  FiniteIntervals.of_fin 634000 200 complete_chunk3170

lemma complete_chunk3171 : ∀ i : Fin 200, Compatible (634200 + i.val) →
    (table.lookup (634200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3171 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 634200 634400 :=
  FiniteIntervals.of_fin 634200 200 complete_chunk3171

lemma complete_chunk3172 : ∀ i : Fin 200, Compatible (634400 + i.val) →
    (table.lookup (634400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3172 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 634400 634600 :=
  FiniteIntervals.of_fin 634400 200 complete_chunk3172

lemma complete_chunk3173 : ∀ i : Fin 200, Compatible (634600 + i.val) →
    (table.lookup (634600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3173 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 634600 634800 :=
  FiniteIntervals.of_fin 634600 200 complete_chunk3173

lemma complete_chunk3174 : ∀ i : Fin 200, Compatible (634800 + i.val) →
    (table.lookup (634800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3174 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 634800 635000 :=
  FiniteIntervals.of_fin 634800 200 complete_chunk3174

lemma complete_chunk3175 : ∀ i : Fin 200, Compatible (635000 + i.val) →
    (table.lookup (635000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3175 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 635000 635200 :=
  FiniteIntervals.of_fin 635000 200 complete_chunk3175

lemma complete_chunk3176 : ∀ i : Fin 200, Compatible (635200 + i.val) →
    (table.lookup (635200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3176 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 635200 635400 :=
  FiniteIntervals.of_fin 635200 200 complete_chunk3176

lemma complete_chunk3177 : ∀ i : Fin 200, Compatible (635400 + i.val) →
    (table.lookup (635400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3177 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 635400 635600 :=
  FiniteIntervals.of_fin 635400 200 complete_chunk3177

lemma complete_chunk3178 : ∀ i : Fin 200, Compatible (635600 + i.val) →
    (table.lookup (635600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3178 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 635600 635800 :=
  FiniteIntervals.of_fin 635600 200 complete_chunk3178

lemma complete_chunk3179 : ∀ i : Fin 200, Compatible (635800 + i.val) →
    (table.lookup (635800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3179 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 635800 636000 :=
  FiniteIntervals.of_fin 635800 200 complete_chunk3179

#print axioms interval_chunk3170
end Erdos184Work.PureFiveFilter4
