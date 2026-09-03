import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4230 : ∀ i : Fin 200, Compatible (846000 + i.val) →
    (table.lookup (846000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4230 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 846000 846200 :=
  FiniteIntervals.of_fin 846000 200 complete_chunk4230

lemma complete_chunk4231 : ∀ i : Fin 200, Compatible (846200 + i.val) →
    (table.lookup (846200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4231 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 846200 846400 :=
  FiniteIntervals.of_fin 846200 200 complete_chunk4231

lemma complete_chunk4232 : ∀ i : Fin 200, Compatible (846400 + i.val) →
    (table.lookup (846400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4232 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 846400 846600 :=
  FiniteIntervals.of_fin 846400 200 complete_chunk4232

lemma complete_chunk4233 : ∀ i : Fin 200, Compatible (846600 + i.val) →
    (table.lookup (846600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4233 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 846600 846800 :=
  FiniteIntervals.of_fin 846600 200 complete_chunk4233

lemma complete_chunk4234 : ∀ i : Fin 200, Compatible (846800 + i.val) →
    (table.lookup (846800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4234 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 846800 847000 :=
  FiniteIntervals.of_fin 846800 200 complete_chunk4234

lemma complete_chunk4235 : ∀ i : Fin 200, Compatible (847000 + i.val) →
    (table.lookup (847000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4235 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 847000 847200 :=
  FiniteIntervals.of_fin 847000 200 complete_chunk4235

lemma complete_chunk4236 : ∀ i : Fin 200, Compatible (847200 + i.val) →
    (table.lookup (847200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4236 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 847200 847400 :=
  FiniteIntervals.of_fin 847200 200 complete_chunk4236

lemma complete_chunk4237 : ∀ i : Fin 200, Compatible (847400 + i.val) →
    (table.lookup (847400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4237 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 847400 847600 :=
  FiniteIntervals.of_fin 847400 200 complete_chunk4237

lemma complete_chunk4238 : ∀ i : Fin 200, Compatible (847600 + i.val) →
    (table.lookup (847600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4238 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 847600 847800 :=
  FiniteIntervals.of_fin 847600 200 complete_chunk4238

lemma complete_chunk4239 : ∀ i : Fin 200, Compatible (847800 + i.val) →
    (table.lookup (847800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4239 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 847800 848000 :=
  FiniteIntervals.of_fin 847800 200 complete_chunk4239

#print axioms interval_chunk4230
end Erdos184Work.PureFiveFilter4
