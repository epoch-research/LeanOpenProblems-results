import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk160 : ∀ i : Fin 200, Compatible (32000 + i.val) →
    (table.lookup (32000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk160 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 32000 32200 :=
  FiniteIntervals.of_fin 32000 200 complete_chunk160

lemma complete_chunk161 : ∀ i : Fin 200, Compatible (32200 + i.val) →
    (table.lookup (32200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk161 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 32200 32400 :=
  FiniteIntervals.of_fin 32200 200 complete_chunk161

lemma complete_chunk162 : ∀ i : Fin 200, Compatible (32400 + i.val) →
    (table.lookup (32400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk162 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 32400 32600 :=
  FiniteIntervals.of_fin 32400 200 complete_chunk162

lemma complete_chunk163 : ∀ i : Fin 200, Compatible (32600 + i.val) →
    (table.lookup (32600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk163 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 32600 32800 :=
  FiniteIntervals.of_fin 32600 200 complete_chunk163

lemma complete_chunk164 : ∀ i : Fin 200, Compatible (32800 + i.val) →
    (table.lookup (32800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk164 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 32800 33000 :=
  FiniteIntervals.of_fin 32800 200 complete_chunk164

lemma complete_chunk165 : ∀ i : Fin 200, Compatible (33000 + i.val) →
    (table.lookup (33000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk165 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 33000 33200 :=
  FiniteIntervals.of_fin 33000 200 complete_chunk165

lemma complete_chunk166 : ∀ i : Fin 200, Compatible (33200 + i.val) →
    (table.lookup (33200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk166 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 33200 33400 :=
  FiniteIntervals.of_fin 33200 200 complete_chunk166

lemma complete_chunk167 : ∀ i : Fin 200, Compatible (33400 + i.val) →
    (table.lookup (33400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk167 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 33400 33600 :=
  FiniteIntervals.of_fin 33400 200 complete_chunk167

lemma complete_chunk168 : ∀ i : Fin 200, Compatible (33600 + i.val) →
    (table.lookup (33600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk168 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 33600 33800 :=
  FiniteIntervals.of_fin 33600 200 complete_chunk168

lemma complete_chunk169 : ∀ i : Fin 200, Compatible (33800 + i.val) →
    (table.lookup (33800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk169 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 33800 34000 :=
  FiniteIntervals.of_fin 33800 200 complete_chunk169

#print axioms interval_chunk160
end Erdos184Work.PureFiveFilter3
