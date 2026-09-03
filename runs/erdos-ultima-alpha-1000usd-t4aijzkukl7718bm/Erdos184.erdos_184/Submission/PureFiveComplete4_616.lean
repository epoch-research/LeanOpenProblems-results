import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6160 : ∀ i : Fin 200, Compatible (1232000 + i.val) →
    (table.lookup (1232000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6160 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1232000 1232200 :=
  FiniteIntervals.of_fin 1232000 200 complete_chunk6160

lemma complete_chunk6161 : ∀ i : Fin 200, Compatible (1232200 + i.val) →
    (table.lookup (1232200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6161 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1232200 1232400 :=
  FiniteIntervals.of_fin 1232200 200 complete_chunk6161

lemma complete_chunk6162 : ∀ i : Fin 200, Compatible (1232400 + i.val) →
    (table.lookup (1232400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6162 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1232400 1232600 :=
  FiniteIntervals.of_fin 1232400 200 complete_chunk6162

lemma complete_chunk6163 : ∀ i : Fin 200, Compatible (1232600 + i.val) →
    (table.lookup (1232600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6163 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1232600 1232800 :=
  FiniteIntervals.of_fin 1232600 200 complete_chunk6163

lemma complete_chunk6164 : ∀ i : Fin 200, Compatible (1232800 + i.val) →
    (table.lookup (1232800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6164 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1232800 1233000 :=
  FiniteIntervals.of_fin 1232800 200 complete_chunk6164

lemma complete_chunk6165 : ∀ i : Fin 200, Compatible (1233000 + i.val) →
    (table.lookup (1233000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6165 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1233000 1233200 :=
  FiniteIntervals.of_fin 1233000 200 complete_chunk6165

lemma complete_chunk6166 : ∀ i : Fin 200, Compatible (1233200 + i.val) →
    (table.lookup (1233200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6166 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1233200 1233400 :=
  FiniteIntervals.of_fin 1233200 200 complete_chunk6166

lemma complete_chunk6167 : ∀ i : Fin 200, Compatible (1233400 + i.val) →
    (table.lookup (1233400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6167 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1233400 1233600 :=
  FiniteIntervals.of_fin 1233400 200 complete_chunk6167

lemma complete_chunk6168 : ∀ i : Fin 200, Compatible (1233600 + i.val) →
    (table.lookup (1233600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6168 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1233600 1233800 :=
  FiniteIntervals.of_fin 1233600 200 complete_chunk6168

lemma complete_chunk6169 : ∀ i : Fin 200, Compatible (1233800 + i.val) →
    (table.lookup (1233800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6169 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1233800 1234000 :=
  FiniteIntervals.of_fin 1233800 200 complete_chunk6169

#print axioms interval_chunk6160
end Erdos184Work.PureFiveFilter4
