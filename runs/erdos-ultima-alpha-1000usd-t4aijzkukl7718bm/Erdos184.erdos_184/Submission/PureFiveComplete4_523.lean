import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5230 : ∀ i : Fin 200, Compatible (1046000 + i.val) →
    (table.lookup (1046000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5230 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1046000 1046200 :=
  FiniteIntervals.of_fin 1046000 200 complete_chunk5230

lemma complete_chunk5231 : ∀ i : Fin 200, Compatible (1046200 + i.val) →
    (table.lookup (1046200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5231 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1046200 1046400 :=
  FiniteIntervals.of_fin 1046200 200 complete_chunk5231

lemma complete_chunk5232 : ∀ i : Fin 200, Compatible (1046400 + i.val) →
    (table.lookup (1046400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5232 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1046400 1046600 :=
  FiniteIntervals.of_fin 1046400 200 complete_chunk5232

lemma complete_chunk5233 : ∀ i : Fin 200, Compatible (1046600 + i.val) →
    (table.lookup (1046600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5233 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1046600 1046800 :=
  FiniteIntervals.of_fin 1046600 200 complete_chunk5233

lemma complete_chunk5234 : ∀ i : Fin 200, Compatible (1046800 + i.val) →
    (table.lookup (1046800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5234 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1046800 1047000 :=
  FiniteIntervals.of_fin 1046800 200 complete_chunk5234

lemma complete_chunk5235 : ∀ i : Fin 200, Compatible (1047000 + i.val) →
    (table.lookup (1047000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5235 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1047000 1047200 :=
  FiniteIntervals.of_fin 1047000 200 complete_chunk5235

lemma complete_chunk5236 : ∀ i : Fin 200, Compatible (1047200 + i.val) →
    (table.lookup (1047200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5236 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1047200 1047400 :=
  FiniteIntervals.of_fin 1047200 200 complete_chunk5236

lemma complete_chunk5237 : ∀ i : Fin 200, Compatible (1047400 + i.val) →
    (table.lookup (1047400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5237 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1047400 1047600 :=
  FiniteIntervals.of_fin 1047400 200 complete_chunk5237

lemma complete_chunk5238 : ∀ i : Fin 200, Compatible (1047600 + i.val) →
    (table.lookup (1047600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5238 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1047600 1047800 :=
  FiniteIntervals.of_fin 1047600 200 complete_chunk5238

lemma complete_chunk5239 : ∀ i : Fin 200, Compatible (1047800 + i.val) →
    (table.lookup (1047800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5239 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1047800 1048000 :=
  FiniteIntervals.of_fin 1047800 200 complete_chunk5239

#print axioms interval_chunk5230
end Erdos184Work.PureFiveFilter4
