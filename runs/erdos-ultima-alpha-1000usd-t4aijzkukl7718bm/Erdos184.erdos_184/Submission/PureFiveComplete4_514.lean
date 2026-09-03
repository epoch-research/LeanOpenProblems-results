import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5140 : ∀ i : Fin 200, Compatible (1028000 + i.val) →
    (table.lookup (1028000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5140 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1028000 1028200 :=
  FiniteIntervals.of_fin 1028000 200 complete_chunk5140

lemma complete_chunk5141 : ∀ i : Fin 200, Compatible (1028200 + i.val) →
    (table.lookup (1028200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5141 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1028200 1028400 :=
  FiniteIntervals.of_fin 1028200 200 complete_chunk5141

lemma complete_chunk5142 : ∀ i : Fin 200, Compatible (1028400 + i.val) →
    (table.lookup (1028400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5142 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1028400 1028600 :=
  FiniteIntervals.of_fin 1028400 200 complete_chunk5142

lemma complete_chunk5143 : ∀ i : Fin 200, Compatible (1028600 + i.val) →
    (table.lookup (1028600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5143 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1028600 1028800 :=
  FiniteIntervals.of_fin 1028600 200 complete_chunk5143

lemma complete_chunk5144 : ∀ i : Fin 200, Compatible (1028800 + i.val) →
    (table.lookup (1028800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5144 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1028800 1029000 :=
  FiniteIntervals.of_fin 1028800 200 complete_chunk5144

lemma complete_chunk5145 : ∀ i : Fin 200, Compatible (1029000 + i.val) →
    (table.lookup (1029000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5145 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1029000 1029200 :=
  FiniteIntervals.of_fin 1029000 200 complete_chunk5145

lemma complete_chunk5146 : ∀ i : Fin 200, Compatible (1029200 + i.val) →
    (table.lookup (1029200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5146 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1029200 1029400 :=
  FiniteIntervals.of_fin 1029200 200 complete_chunk5146

lemma complete_chunk5147 : ∀ i : Fin 200, Compatible (1029400 + i.val) →
    (table.lookup (1029400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5147 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1029400 1029600 :=
  FiniteIntervals.of_fin 1029400 200 complete_chunk5147

lemma complete_chunk5148 : ∀ i : Fin 200, Compatible (1029600 + i.val) →
    (table.lookup (1029600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5148 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1029600 1029800 :=
  FiniteIntervals.of_fin 1029600 200 complete_chunk5148

lemma complete_chunk5149 : ∀ i : Fin 200, Compatible (1029800 + i.val) →
    (table.lookup (1029800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5149 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1029800 1030000 :=
  FiniteIntervals.of_fin 1029800 200 complete_chunk5149

#print axioms interval_chunk5140
end Erdos184Work.PureFiveFilter4
