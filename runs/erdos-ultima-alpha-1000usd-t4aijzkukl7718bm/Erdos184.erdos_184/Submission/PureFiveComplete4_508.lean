import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5080 : ∀ i : Fin 200, Compatible (1016000 + i.val) →
    (table.lookup (1016000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5080 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1016000 1016200 :=
  FiniteIntervals.of_fin 1016000 200 complete_chunk5080

lemma complete_chunk5081 : ∀ i : Fin 200, Compatible (1016200 + i.val) →
    (table.lookup (1016200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5081 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1016200 1016400 :=
  FiniteIntervals.of_fin 1016200 200 complete_chunk5081

lemma complete_chunk5082 : ∀ i : Fin 200, Compatible (1016400 + i.val) →
    (table.lookup (1016400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5082 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1016400 1016600 :=
  FiniteIntervals.of_fin 1016400 200 complete_chunk5082

lemma complete_chunk5083 : ∀ i : Fin 200, Compatible (1016600 + i.val) →
    (table.lookup (1016600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5083 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1016600 1016800 :=
  FiniteIntervals.of_fin 1016600 200 complete_chunk5083

lemma complete_chunk5084 : ∀ i : Fin 200, Compatible (1016800 + i.val) →
    (table.lookup (1016800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5084 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1016800 1017000 :=
  FiniteIntervals.of_fin 1016800 200 complete_chunk5084

lemma complete_chunk5085 : ∀ i : Fin 200, Compatible (1017000 + i.val) →
    (table.lookup (1017000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5085 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1017000 1017200 :=
  FiniteIntervals.of_fin 1017000 200 complete_chunk5085

lemma complete_chunk5086 : ∀ i : Fin 200, Compatible (1017200 + i.val) →
    (table.lookup (1017200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5086 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1017200 1017400 :=
  FiniteIntervals.of_fin 1017200 200 complete_chunk5086

lemma complete_chunk5087 : ∀ i : Fin 200, Compatible (1017400 + i.val) →
    (table.lookup (1017400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5087 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1017400 1017600 :=
  FiniteIntervals.of_fin 1017400 200 complete_chunk5087

lemma complete_chunk5088 : ∀ i : Fin 200, Compatible (1017600 + i.val) →
    (table.lookup (1017600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5088 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1017600 1017800 :=
  FiniteIntervals.of_fin 1017600 200 complete_chunk5088

lemma complete_chunk5089 : ∀ i : Fin 200, Compatible (1017800 + i.val) →
    (table.lookup (1017800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5089 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1017800 1018000 :=
  FiniteIntervals.of_fin 1017800 200 complete_chunk5089

#print axioms interval_chunk5080
end Erdos184Work.PureFiveFilter4
