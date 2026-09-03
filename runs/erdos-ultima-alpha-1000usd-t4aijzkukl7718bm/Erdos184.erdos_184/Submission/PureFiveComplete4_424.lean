import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4240 : ∀ i : Fin 200, Compatible (848000 + i.val) →
    (table.lookup (848000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4240 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 848000 848200 :=
  FiniteIntervals.of_fin 848000 200 complete_chunk4240

lemma complete_chunk4241 : ∀ i : Fin 200, Compatible (848200 + i.val) →
    (table.lookup (848200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4241 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 848200 848400 :=
  FiniteIntervals.of_fin 848200 200 complete_chunk4241

lemma complete_chunk4242 : ∀ i : Fin 200, Compatible (848400 + i.val) →
    (table.lookup (848400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4242 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 848400 848600 :=
  FiniteIntervals.of_fin 848400 200 complete_chunk4242

lemma complete_chunk4243 : ∀ i : Fin 200, Compatible (848600 + i.val) →
    (table.lookup (848600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4243 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 848600 848800 :=
  FiniteIntervals.of_fin 848600 200 complete_chunk4243

lemma complete_chunk4244 : ∀ i : Fin 200, Compatible (848800 + i.val) →
    (table.lookup (848800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4244 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 848800 849000 :=
  FiniteIntervals.of_fin 848800 200 complete_chunk4244

lemma complete_chunk4245 : ∀ i : Fin 200, Compatible (849000 + i.val) →
    (table.lookup (849000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4245 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 849000 849200 :=
  FiniteIntervals.of_fin 849000 200 complete_chunk4245

lemma complete_chunk4246 : ∀ i : Fin 200, Compatible (849200 + i.val) →
    (table.lookup (849200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4246 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 849200 849400 :=
  FiniteIntervals.of_fin 849200 200 complete_chunk4246

lemma complete_chunk4247 : ∀ i : Fin 200, Compatible (849400 + i.val) →
    (table.lookup (849400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4247 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 849400 849600 :=
  FiniteIntervals.of_fin 849400 200 complete_chunk4247

lemma complete_chunk4248 : ∀ i : Fin 200, Compatible (849600 + i.val) →
    (table.lookup (849600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4248 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 849600 849800 :=
  FiniteIntervals.of_fin 849600 200 complete_chunk4248

lemma complete_chunk4249 : ∀ i : Fin 200, Compatible (849800 + i.val) →
    (table.lookup (849800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4249 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 849800 850000 :=
  FiniteIntervals.of_fin 849800 200 complete_chunk4249

#print axioms interval_chunk4240
end Erdos184Work.PureFiveFilter4
