import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4260 : ∀ i : Fin 200, Compatible (852000 + i.val) →
    (table.lookup (852000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4260 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 852000 852200 :=
  FiniteIntervals.of_fin 852000 200 complete_chunk4260

lemma complete_chunk4261 : ∀ i : Fin 200, Compatible (852200 + i.val) →
    (table.lookup (852200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4261 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 852200 852400 :=
  FiniteIntervals.of_fin 852200 200 complete_chunk4261

lemma complete_chunk4262 : ∀ i : Fin 200, Compatible (852400 + i.val) →
    (table.lookup (852400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4262 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 852400 852600 :=
  FiniteIntervals.of_fin 852400 200 complete_chunk4262

lemma complete_chunk4263 : ∀ i : Fin 200, Compatible (852600 + i.val) →
    (table.lookup (852600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4263 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 852600 852800 :=
  FiniteIntervals.of_fin 852600 200 complete_chunk4263

lemma complete_chunk4264 : ∀ i : Fin 200, Compatible (852800 + i.val) →
    (table.lookup (852800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4264 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 852800 853000 :=
  FiniteIntervals.of_fin 852800 200 complete_chunk4264

lemma complete_chunk4265 : ∀ i : Fin 200, Compatible (853000 + i.val) →
    (table.lookup (853000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4265 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 853000 853200 :=
  FiniteIntervals.of_fin 853000 200 complete_chunk4265

lemma complete_chunk4266 : ∀ i : Fin 200, Compatible (853200 + i.val) →
    (table.lookup (853200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4266 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 853200 853400 :=
  FiniteIntervals.of_fin 853200 200 complete_chunk4266

lemma complete_chunk4267 : ∀ i : Fin 200, Compatible (853400 + i.val) →
    (table.lookup (853400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4267 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 853400 853600 :=
  FiniteIntervals.of_fin 853400 200 complete_chunk4267

lemma complete_chunk4268 : ∀ i : Fin 200, Compatible (853600 + i.val) →
    (table.lookup (853600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4268 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 853600 853800 :=
  FiniteIntervals.of_fin 853600 200 complete_chunk4268

lemma complete_chunk4269 : ∀ i : Fin 200, Compatible (853800 + i.val) →
    (table.lookup (853800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4269 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 853800 854000 :=
  FiniteIntervals.of_fin 853800 200 complete_chunk4269

#print axioms interval_chunk4260
end Erdos184Work.PureFiveFilter4
