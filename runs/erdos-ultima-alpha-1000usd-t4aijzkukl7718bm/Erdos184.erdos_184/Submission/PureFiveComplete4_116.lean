import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1160 : ∀ i : Fin 200, Compatible (232000 + i.val) →
    (table.lookup (232000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1160 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 232000 232200 :=
  FiniteIntervals.of_fin 232000 200 complete_chunk1160

lemma complete_chunk1161 : ∀ i : Fin 200, Compatible (232200 + i.val) →
    (table.lookup (232200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1161 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 232200 232400 :=
  FiniteIntervals.of_fin 232200 200 complete_chunk1161

lemma complete_chunk1162 : ∀ i : Fin 200, Compatible (232400 + i.val) →
    (table.lookup (232400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1162 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 232400 232600 :=
  FiniteIntervals.of_fin 232400 200 complete_chunk1162

lemma complete_chunk1163 : ∀ i : Fin 200, Compatible (232600 + i.val) →
    (table.lookup (232600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1163 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 232600 232800 :=
  FiniteIntervals.of_fin 232600 200 complete_chunk1163

lemma complete_chunk1164 : ∀ i : Fin 200, Compatible (232800 + i.val) →
    (table.lookup (232800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1164 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 232800 233000 :=
  FiniteIntervals.of_fin 232800 200 complete_chunk1164

lemma complete_chunk1165 : ∀ i : Fin 200, Compatible (233000 + i.val) →
    (table.lookup (233000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1165 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 233000 233200 :=
  FiniteIntervals.of_fin 233000 200 complete_chunk1165

lemma complete_chunk1166 : ∀ i : Fin 200, Compatible (233200 + i.val) →
    (table.lookup (233200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1166 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 233200 233400 :=
  FiniteIntervals.of_fin 233200 200 complete_chunk1166

lemma complete_chunk1167 : ∀ i : Fin 200, Compatible (233400 + i.val) →
    (table.lookup (233400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1167 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 233400 233600 :=
  FiniteIntervals.of_fin 233400 200 complete_chunk1167

lemma complete_chunk1168 : ∀ i : Fin 200, Compatible (233600 + i.val) →
    (table.lookup (233600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1168 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 233600 233800 :=
  FiniteIntervals.of_fin 233600 200 complete_chunk1168

lemma complete_chunk1169 : ∀ i : Fin 200, Compatible (233800 + i.val) →
    (table.lookup (233800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1169 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 233800 234000 :=
  FiniteIntervals.of_fin 233800 200 complete_chunk1169

#print axioms interval_chunk1160
end Erdos184Work.PureFiveFilter4
