import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk140 : ∀ i : Fin 200, Compatible (28000 + i.val) →
    (table.lookup (28000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk140 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 28000 28200 :=
  FiniteIntervals.of_fin 28000 200 complete_chunk140

lemma complete_chunk141 : ∀ i : Fin 200, Compatible (28200 + i.val) →
    (table.lookup (28200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk141 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 28200 28400 :=
  FiniteIntervals.of_fin 28200 200 complete_chunk141

lemma complete_chunk142 : ∀ i : Fin 200, Compatible (28400 + i.val) →
    (table.lookup (28400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk142 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 28400 28600 :=
  FiniteIntervals.of_fin 28400 200 complete_chunk142

lemma complete_chunk143 : ∀ i : Fin 200, Compatible (28600 + i.val) →
    (table.lookup (28600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk143 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 28600 28800 :=
  FiniteIntervals.of_fin 28600 200 complete_chunk143

lemma complete_chunk144 : ∀ i : Fin 200, Compatible (28800 + i.val) →
    (table.lookup (28800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk144 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 28800 29000 :=
  FiniteIntervals.of_fin 28800 200 complete_chunk144

lemma complete_chunk145 : ∀ i : Fin 200, Compatible (29000 + i.val) →
    (table.lookup (29000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk145 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 29000 29200 :=
  FiniteIntervals.of_fin 29000 200 complete_chunk145

lemma complete_chunk146 : ∀ i : Fin 200, Compatible (29200 + i.val) →
    (table.lookup (29200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk146 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 29200 29400 :=
  FiniteIntervals.of_fin 29200 200 complete_chunk146

lemma complete_chunk147 : ∀ i : Fin 200, Compatible (29400 + i.val) →
    (table.lookup (29400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk147 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 29400 29600 :=
  FiniteIntervals.of_fin 29400 200 complete_chunk147

lemma complete_chunk148 : ∀ i : Fin 200, Compatible (29600 + i.val) →
    (table.lookup (29600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk148 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 29600 29800 :=
  FiniteIntervals.of_fin 29600 200 complete_chunk148

lemma complete_chunk149 : ∀ i : Fin 200, Compatible (29800 + i.val) →
    (table.lookup (29800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk149 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 29800 30000 :=
  FiniteIntervals.of_fin 29800 200 complete_chunk149

#print axioms interval_chunk140
end Erdos184Work.PureFiveFilter3
