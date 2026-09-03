import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5130 : ∀ i : Fin 200, Compatible (1026000 + i.val) →
    (table.lookup (1026000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5130 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1026000 1026200 :=
  FiniteIntervals.of_fin 1026000 200 complete_chunk5130

lemma complete_chunk5131 : ∀ i : Fin 200, Compatible (1026200 + i.val) →
    (table.lookup (1026200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5131 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1026200 1026400 :=
  FiniteIntervals.of_fin 1026200 200 complete_chunk5131

lemma complete_chunk5132 : ∀ i : Fin 200, Compatible (1026400 + i.val) →
    (table.lookup (1026400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5132 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1026400 1026600 :=
  FiniteIntervals.of_fin 1026400 200 complete_chunk5132

lemma complete_chunk5133 : ∀ i : Fin 200, Compatible (1026600 + i.val) →
    (table.lookup (1026600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5133 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1026600 1026800 :=
  FiniteIntervals.of_fin 1026600 200 complete_chunk5133

lemma complete_chunk5134 : ∀ i : Fin 200, Compatible (1026800 + i.val) →
    (table.lookup (1026800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5134 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1026800 1027000 :=
  FiniteIntervals.of_fin 1026800 200 complete_chunk5134

lemma complete_chunk5135 : ∀ i : Fin 200, Compatible (1027000 + i.val) →
    (table.lookup (1027000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5135 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1027000 1027200 :=
  FiniteIntervals.of_fin 1027000 200 complete_chunk5135

lemma complete_chunk5136 : ∀ i : Fin 200, Compatible (1027200 + i.val) →
    (table.lookup (1027200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5136 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1027200 1027400 :=
  FiniteIntervals.of_fin 1027200 200 complete_chunk5136

lemma complete_chunk5137 : ∀ i : Fin 200, Compatible (1027400 + i.val) →
    (table.lookup (1027400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5137 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1027400 1027600 :=
  FiniteIntervals.of_fin 1027400 200 complete_chunk5137

lemma complete_chunk5138 : ∀ i : Fin 200, Compatible (1027600 + i.val) →
    (table.lookup (1027600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5138 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1027600 1027800 :=
  FiniteIntervals.of_fin 1027600 200 complete_chunk5138

lemma complete_chunk5139 : ∀ i : Fin 200, Compatible (1027800 + i.val) →
    (table.lookup (1027800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5139 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1027800 1028000 :=
  FiniteIntervals.of_fin 1027800 200 complete_chunk5139

#print axioms interval_chunk5130
end Erdos184Work.PureFiveFilter4
