import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3130 : ∀ i : Fin 200, Compatible (626000 + i.val) →
    (table.lookup (626000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3130 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 626000 626200 :=
  FiniteIntervals.of_fin 626000 200 complete_chunk3130

lemma complete_chunk3131 : ∀ i : Fin 200, Compatible (626200 + i.val) →
    (table.lookup (626200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3131 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 626200 626400 :=
  FiniteIntervals.of_fin 626200 200 complete_chunk3131

lemma complete_chunk3132 : ∀ i : Fin 200, Compatible (626400 + i.val) →
    (table.lookup (626400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3132 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 626400 626600 :=
  FiniteIntervals.of_fin 626400 200 complete_chunk3132

lemma complete_chunk3133 : ∀ i : Fin 200, Compatible (626600 + i.val) →
    (table.lookup (626600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3133 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 626600 626800 :=
  FiniteIntervals.of_fin 626600 200 complete_chunk3133

lemma complete_chunk3134 : ∀ i : Fin 200, Compatible (626800 + i.val) →
    (table.lookup (626800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3134 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 626800 627000 :=
  FiniteIntervals.of_fin 626800 200 complete_chunk3134

lemma complete_chunk3135 : ∀ i : Fin 200, Compatible (627000 + i.val) →
    (table.lookup (627000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3135 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 627000 627200 :=
  FiniteIntervals.of_fin 627000 200 complete_chunk3135

lemma complete_chunk3136 : ∀ i : Fin 200, Compatible (627200 + i.val) →
    (table.lookup (627200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3136 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 627200 627400 :=
  FiniteIntervals.of_fin 627200 200 complete_chunk3136

lemma complete_chunk3137 : ∀ i : Fin 200, Compatible (627400 + i.val) →
    (table.lookup (627400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3137 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 627400 627600 :=
  FiniteIntervals.of_fin 627400 200 complete_chunk3137

lemma complete_chunk3138 : ∀ i : Fin 200, Compatible (627600 + i.val) →
    (table.lookup (627600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3138 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 627600 627800 :=
  FiniteIntervals.of_fin 627600 200 complete_chunk3138

lemma complete_chunk3139 : ∀ i : Fin 200, Compatible (627800 + i.val) →
    (table.lookup (627800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3139 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 627800 628000 :=
  FiniteIntervals.of_fin 627800 200 complete_chunk3139

#print axioms interval_chunk3130
end Erdos184Work.PureFiveFilter4
