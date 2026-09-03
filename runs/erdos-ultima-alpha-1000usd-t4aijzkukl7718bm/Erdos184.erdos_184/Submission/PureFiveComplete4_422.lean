import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4220 : ∀ i : Fin 200, Compatible (844000 + i.val) →
    (table.lookup (844000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4220 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 844000 844200 :=
  FiniteIntervals.of_fin 844000 200 complete_chunk4220

lemma complete_chunk4221 : ∀ i : Fin 200, Compatible (844200 + i.val) →
    (table.lookup (844200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4221 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 844200 844400 :=
  FiniteIntervals.of_fin 844200 200 complete_chunk4221

lemma complete_chunk4222 : ∀ i : Fin 200, Compatible (844400 + i.val) →
    (table.lookup (844400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4222 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 844400 844600 :=
  FiniteIntervals.of_fin 844400 200 complete_chunk4222

lemma complete_chunk4223 : ∀ i : Fin 200, Compatible (844600 + i.val) →
    (table.lookup (844600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4223 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 844600 844800 :=
  FiniteIntervals.of_fin 844600 200 complete_chunk4223

lemma complete_chunk4224 : ∀ i : Fin 200, Compatible (844800 + i.val) →
    (table.lookup (844800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4224 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 844800 845000 :=
  FiniteIntervals.of_fin 844800 200 complete_chunk4224

lemma complete_chunk4225 : ∀ i : Fin 200, Compatible (845000 + i.val) →
    (table.lookup (845000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4225 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 845000 845200 :=
  FiniteIntervals.of_fin 845000 200 complete_chunk4225

lemma complete_chunk4226 : ∀ i : Fin 200, Compatible (845200 + i.val) →
    (table.lookup (845200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4226 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 845200 845400 :=
  FiniteIntervals.of_fin 845200 200 complete_chunk4226

lemma complete_chunk4227 : ∀ i : Fin 200, Compatible (845400 + i.val) →
    (table.lookup (845400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4227 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 845400 845600 :=
  FiniteIntervals.of_fin 845400 200 complete_chunk4227

lemma complete_chunk4228 : ∀ i : Fin 200, Compatible (845600 + i.val) →
    (table.lookup (845600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4228 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 845600 845800 :=
  FiniteIntervals.of_fin 845600 200 complete_chunk4228

lemma complete_chunk4229 : ∀ i : Fin 200, Compatible (845800 + i.val) →
    (table.lookup (845800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4229 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 845800 846000 :=
  FiniteIntervals.of_fin 845800 200 complete_chunk4229

#print axioms interval_chunk4220
end Erdos184Work.PureFiveFilter4
