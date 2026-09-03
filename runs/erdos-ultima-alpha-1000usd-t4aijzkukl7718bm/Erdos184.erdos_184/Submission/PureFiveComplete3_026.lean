import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk260 : ∀ i : Fin 200, Compatible (52000 + i.val) →
    (table.lookup (52000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk260 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52000 52200 :=
  FiniteIntervals.of_fin 52000 200 complete_chunk260

lemma complete_chunk261 : ∀ i : Fin 200, Compatible (52200 + i.val) →
    (table.lookup (52200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk261 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52200 52400 :=
  FiniteIntervals.of_fin 52200 200 complete_chunk261

lemma complete_chunk262 : ∀ i : Fin 200, Compatible (52400 + i.val) →
    (table.lookup (52400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk262 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52400 52600 :=
  FiniteIntervals.of_fin 52400 200 complete_chunk262

lemma complete_chunk263 : ∀ i : Fin 200, Compatible (52600 + i.val) →
    (table.lookup (52600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk263 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52600 52800 :=
  FiniteIntervals.of_fin 52600 200 complete_chunk263

lemma complete_chunk264 : ∀ i : Fin 200, Compatible (52800 + i.val) →
    (table.lookup (52800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk264 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52800 53000 :=
  FiniteIntervals.of_fin 52800 200 complete_chunk264

lemma complete_chunk265 : ∀ i : Fin 200, Compatible (53000 + i.val) →
    (table.lookup (53000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk265 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53000 53200 :=
  FiniteIntervals.of_fin 53000 200 complete_chunk265

lemma complete_chunk266 : ∀ i : Fin 200, Compatible (53200 + i.val) →
    (table.lookup (53200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk266 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53200 53400 :=
  FiniteIntervals.of_fin 53200 200 complete_chunk266

lemma complete_chunk267 : ∀ i : Fin 200, Compatible (53400 + i.val) →
    (table.lookup (53400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk267 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53400 53600 :=
  FiniteIntervals.of_fin 53400 200 complete_chunk267

lemma complete_chunk268 : ∀ i : Fin 200, Compatible (53600 + i.val) →
    (table.lookup (53600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk268 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53600 53800 :=
  FiniteIntervals.of_fin 53600 200 complete_chunk268

lemma complete_chunk269 : ∀ i : Fin 200, Compatible (53800 + i.val) →
    (table.lookup (53800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk269 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53800 54000 :=
  FiniteIntervals.of_fin 53800 200 complete_chunk269

#print axioms interval_chunk260
end Erdos184Work.PureFiveFilter3
