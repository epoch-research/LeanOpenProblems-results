import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4110 : ∀ i : Fin 200, Compatible (822000 + i.val) →
    (table.lookup (822000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4110 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 822000 822200 :=
  FiniteIntervals.of_fin 822000 200 complete_chunk4110

lemma complete_chunk4111 : ∀ i : Fin 200, Compatible (822200 + i.val) →
    (table.lookup (822200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4111 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 822200 822400 :=
  FiniteIntervals.of_fin 822200 200 complete_chunk4111

lemma complete_chunk4112 : ∀ i : Fin 200, Compatible (822400 + i.val) →
    (table.lookup (822400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4112 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 822400 822600 :=
  FiniteIntervals.of_fin 822400 200 complete_chunk4112

lemma complete_chunk4113 : ∀ i : Fin 200, Compatible (822600 + i.val) →
    (table.lookup (822600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4113 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 822600 822800 :=
  FiniteIntervals.of_fin 822600 200 complete_chunk4113

lemma complete_chunk4114 : ∀ i : Fin 200, Compatible (822800 + i.val) →
    (table.lookup (822800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4114 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 822800 823000 :=
  FiniteIntervals.of_fin 822800 200 complete_chunk4114

lemma complete_chunk4115 : ∀ i : Fin 200, Compatible (823000 + i.val) →
    (table.lookup (823000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4115 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 823000 823200 :=
  FiniteIntervals.of_fin 823000 200 complete_chunk4115

lemma complete_chunk4116 : ∀ i : Fin 200, Compatible (823200 + i.val) →
    (table.lookup (823200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4116 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 823200 823400 :=
  FiniteIntervals.of_fin 823200 200 complete_chunk4116

lemma complete_chunk4117 : ∀ i : Fin 200, Compatible (823400 + i.val) →
    (table.lookup (823400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4117 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 823400 823600 :=
  FiniteIntervals.of_fin 823400 200 complete_chunk4117

lemma complete_chunk4118 : ∀ i : Fin 200, Compatible (823600 + i.val) →
    (table.lookup (823600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4118 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 823600 823800 :=
  FiniteIntervals.of_fin 823600 200 complete_chunk4118

lemma complete_chunk4119 : ∀ i : Fin 200, Compatible (823800 + i.val) →
    (table.lookup (823800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4119 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 823800 824000 :=
  FiniteIntervals.of_fin 823800 200 complete_chunk4119

#print axioms interval_chunk4110
end Erdos184Work.PureFiveFilter4
