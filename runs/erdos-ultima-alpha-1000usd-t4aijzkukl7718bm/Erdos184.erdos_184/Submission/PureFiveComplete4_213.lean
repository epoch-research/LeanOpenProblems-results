import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2130 : ∀ i : Fin 200, Compatible (426000 + i.val) →
    (table.lookup (426000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2130 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 426000 426200 :=
  FiniteIntervals.of_fin 426000 200 complete_chunk2130

lemma complete_chunk2131 : ∀ i : Fin 200, Compatible (426200 + i.val) →
    (table.lookup (426200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2131 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 426200 426400 :=
  FiniteIntervals.of_fin 426200 200 complete_chunk2131

lemma complete_chunk2132 : ∀ i : Fin 200, Compatible (426400 + i.val) →
    (table.lookup (426400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2132 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 426400 426600 :=
  FiniteIntervals.of_fin 426400 200 complete_chunk2132

lemma complete_chunk2133 : ∀ i : Fin 200, Compatible (426600 + i.val) →
    (table.lookup (426600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2133 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 426600 426800 :=
  FiniteIntervals.of_fin 426600 200 complete_chunk2133

lemma complete_chunk2134 : ∀ i : Fin 200, Compatible (426800 + i.val) →
    (table.lookup (426800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2134 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 426800 427000 :=
  FiniteIntervals.of_fin 426800 200 complete_chunk2134

lemma complete_chunk2135 : ∀ i : Fin 200, Compatible (427000 + i.val) →
    (table.lookup (427000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2135 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 427000 427200 :=
  FiniteIntervals.of_fin 427000 200 complete_chunk2135

lemma complete_chunk2136 : ∀ i : Fin 200, Compatible (427200 + i.val) →
    (table.lookup (427200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2136 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 427200 427400 :=
  FiniteIntervals.of_fin 427200 200 complete_chunk2136

lemma complete_chunk2137 : ∀ i : Fin 200, Compatible (427400 + i.val) →
    (table.lookup (427400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2137 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 427400 427600 :=
  FiniteIntervals.of_fin 427400 200 complete_chunk2137

lemma complete_chunk2138 : ∀ i : Fin 200, Compatible (427600 + i.val) →
    (table.lookup (427600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2138 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 427600 427800 :=
  FiniteIntervals.of_fin 427600 200 complete_chunk2138

lemma complete_chunk2139 : ∀ i : Fin 200, Compatible (427800 + i.val) →
    (table.lookup (427800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2139 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 427800 428000 :=
  FiniteIntervals.of_fin 427800 200 complete_chunk2139

#print axioms interval_chunk2130
end Erdos184Work.PureFiveFilter4
