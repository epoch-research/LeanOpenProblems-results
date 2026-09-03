import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk220 : ∀ i : Fin 200, Compatible (44000 + i.val) →
    (table.lookup (44000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk220 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 44000 44200 :=
  FiniteIntervals.of_fin 44000 200 complete_chunk220

lemma complete_chunk221 : ∀ i : Fin 200, Compatible (44200 + i.val) →
    (table.lookup (44200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk221 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 44200 44400 :=
  FiniteIntervals.of_fin 44200 200 complete_chunk221

lemma complete_chunk222 : ∀ i : Fin 200, Compatible (44400 + i.val) →
    (table.lookup (44400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk222 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 44400 44600 :=
  FiniteIntervals.of_fin 44400 200 complete_chunk222

lemma complete_chunk223 : ∀ i : Fin 200, Compatible (44600 + i.val) →
    (table.lookup (44600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk223 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 44600 44800 :=
  FiniteIntervals.of_fin 44600 200 complete_chunk223

lemma complete_chunk224 : ∀ i : Fin 200, Compatible (44800 + i.val) →
    (table.lookup (44800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk224 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 44800 45000 :=
  FiniteIntervals.of_fin 44800 200 complete_chunk224

lemma complete_chunk225 : ∀ i : Fin 200, Compatible (45000 + i.val) →
    (table.lookup (45000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk225 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 45000 45200 :=
  FiniteIntervals.of_fin 45000 200 complete_chunk225

lemma complete_chunk226 : ∀ i : Fin 200, Compatible (45200 + i.val) →
    (table.lookup (45200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk226 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 45200 45400 :=
  FiniteIntervals.of_fin 45200 200 complete_chunk226

lemma complete_chunk227 : ∀ i : Fin 200, Compatible (45400 + i.val) →
    (table.lookup (45400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk227 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 45400 45600 :=
  FiniteIntervals.of_fin 45400 200 complete_chunk227

lemma complete_chunk228 : ∀ i : Fin 200, Compatible (45600 + i.val) →
    (table.lookup (45600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk228 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 45600 45800 :=
  FiniteIntervals.of_fin 45600 200 complete_chunk228

lemma complete_chunk229 : ∀ i : Fin 200, Compatible (45800 + i.val) →
    (table.lookup (45800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk229 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 45800 46000 :=
  FiniteIntervals.of_fin 45800 200 complete_chunk229

#print axioms interval_chunk220
end Erdos184Work.PureFiveFilter3
