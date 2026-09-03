import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5060 : ∀ i : Fin 200, Compatible (1012000 + i.val) →
    (table.lookup (1012000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5060 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1012000 1012200 :=
  FiniteIntervals.of_fin 1012000 200 complete_chunk5060

lemma complete_chunk5061 : ∀ i : Fin 200, Compatible (1012200 + i.val) →
    (table.lookup (1012200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5061 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1012200 1012400 :=
  FiniteIntervals.of_fin 1012200 200 complete_chunk5061

lemma complete_chunk5062 : ∀ i : Fin 200, Compatible (1012400 + i.val) →
    (table.lookup (1012400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5062 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1012400 1012600 :=
  FiniteIntervals.of_fin 1012400 200 complete_chunk5062

lemma complete_chunk5063 : ∀ i : Fin 200, Compatible (1012600 + i.val) →
    (table.lookup (1012600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5063 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1012600 1012800 :=
  FiniteIntervals.of_fin 1012600 200 complete_chunk5063

lemma complete_chunk5064 : ∀ i : Fin 200, Compatible (1012800 + i.val) →
    (table.lookup (1012800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5064 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1012800 1013000 :=
  FiniteIntervals.of_fin 1012800 200 complete_chunk5064

lemma complete_chunk5065 : ∀ i : Fin 200, Compatible (1013000 + i.val) →
    (table.lookup (1013000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5065 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1013000 1013200 :=
  FiniteIntervals.of_fin 1013000 200 complete_chunk5065

lemma complete_chunk5066 : ∀ i : Fin 200, Compatible (1013200 + i.val) →
    (table.lookup (1013200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5066 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1013200 1013400 :=
  FiniteIntervals.of_fin 1013200 200 complete_chunk5066

lemma complete_chunk5067 : ∀ i : Fin 200, Compatible (1013400 + i.val) →
    (table.lookup (1013400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5067 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1013400 1013600 :=
  FiniteIntervals.of_fin 1013400 200 complete_chunk5067

lemma complete_chunk5068 : ∀ i : Fin 200, Compatible (1013600 + i.val) →
    (table.lookup (1013600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5068 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1013600 1013800 :=
  FiniteIntervals.of_fin 1013600 200 complete_chunk5068

lemma complete_chunk5069 : ∀ i : Fin 200, Compatible (1013800 + i.val) →
    (table.lookup (1013800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5069 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1013800 1014000 :=
  FiniteIntervals.of_fin 1013800 200 complete_chunk5069

#print axioms interval_chunk5060
end Erdos184Work.PureFiveFilter4
