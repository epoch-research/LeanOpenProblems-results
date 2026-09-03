import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk180 : ∀ i : Fin 200, Compatible (36000 + i.val) →
    (table.lookup (36000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk180 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 36000 36200 :=
  FiniteIntervals.of_fin 36000 200 complete_chunk180

lemma complete_chunk181 : ∀ i : Fin 200, Compatible (36200 + i.val) →
    (table.lookup (36200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk181 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 36200 36400 :=
  FiniteIntervals.of_fin 36200 200 complete_chunk181

lemma complete_chunk182 : ∀ i : Fin 200, Compatible (36400 + i.val) →
    (table.lookup (36400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk182 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 36400 36600 :=
  FiniteIntervals.of_fin 36400 200 complete_chunk182

lemma complete_chunk183 : ∀ i : Fin 200, Compatible (36600 + i.val) →
    (table.lookup (36600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk183 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 36600 36800 :=
  FiniteIntervals.of_fin 36600 200 complete_chunk183

lemma complete_chunk184 : ∀ i : Fin 200, Compatible (36800 + i.val) →
    (table.lookup (36800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk184 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 36800 37000 :=
  FiniteIntervals.of_fin 36800 200 complete_chunk184

lemma complete_chunk185 : ∀ i : Fin 200, Compatible (37000 + i.val) →
    (table.lookup (37000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk185 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 37000 37200 :=
  FiniteIntervals.of_fin 37000 200 complete_chunk185

lemma complete_chunk186 : ∀ i : Fin 200, Compatible (37200 + i.val) →
    (table.lookup (37200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk186 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 37200 37400 :=
  FiniteIntervals.of_fin 37200 200 complete_chunk186

lemma complete_chunk187 : ∀ i : Fin 200, Compatible (37400 + i.val) →
    (table.lookup (37400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk187 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 37400 37600 :=
  FiniteIntervals.of_fin 37400 200 complete_chunk187

lemma complete_chunk188 : ∀ i : Fin 200, Compatible (37600 + i.val) →
    (table.lookup (37600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk188 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 37600 37800 :=
  FiniteIntervals.of_fin 37600 200 complete_chunk188

lemma complete_chunk189 : ∀ i : Fin 200, Compatible (37800 + i.val) →
    (table.lookup (37800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk189 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 37800 38000 :=
  FiniteIntervals.of_fin 37800 200 complete_chunk189

#print axioms interval_chunk180
end Erdos184Work.PureFiveFilter3
