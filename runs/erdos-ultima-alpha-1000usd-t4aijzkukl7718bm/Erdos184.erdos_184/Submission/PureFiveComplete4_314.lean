import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3140 : ∀ i : Fin 200, Compatible (628000 + i.val) →
    (table.lookup (628000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3140 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 628000 628200 :=
  FiniteIntervals.of_fin 628000 200 complete_chunk3140

lemma complete_chunk3141 : ∀ i : Fin 200, Compatible (628200 + i.val) →
    (table.lookup (628200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3141 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 628200 628400 :=
  FiniteIntervals.of_fin 628200 200 complete_chunk3141

lemma complete_chunk3142 : ∀ i : Fin 200, Compatible (628400 + i.val) →
    (table.lookup (628400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3142 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 628400 628600 :=
  FiniteIntervals.of_fin 628400 200 complete_chunk3142

lemma complete_chunk3143 : ∀ i : Fin 200, Compatible (628600 + i.val) →
    (table.lookup (628600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3143 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 628600 628800 :=
  FiniteIntervals.of_fin 628600 200 complete_chunk3143

lemma complete_chunk3144 : ∀ i : Fin 200, Compatible (628800 + i.val) →
    (table.lookup (628800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3144 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 628800 629000 :=
  FiniteIntervals.of_fin 628800 200 complete_chunk3144

lemma complete_chunk3145 : ∀ i : Fin 200, Compatible (629000 + i.val) →
    (table.lookup (629000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3145 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 629000 629200 :=
  FiniteIntervals.of_fin 629000 200 complete_chunk3145

lemma complete_chunk3146 : ∀ i : Fin 200, Compatible (629200 + i.val) →
    (table.lookup (629200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3146 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 629200 629400 :=
  FiniteIntervals.of_fin 629200 200 complete_chunk3146

lemma complete_chunk3147 : ∀ i : Fin 200, Compatible (629400 + i.val) →
    (table.lookup (629400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3147 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 629400 629600 :=
  FiniteIntervals.of_fin 629400 200 complete_chunk3147

lemma complete_chunk3148 : ∀ i : Fin 200, Compatible (629600 + i.val) →
    (table.lookup (629600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3148 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 629600 629800 :=
  FiniteIntervals.of_fin 629600 200 complete_chunk3148

lemma complete_chunk3149 : ∀ i : Fin 200, Compatible (629800 + i.val) →
    (table.lookup (629800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3149 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 629800 630000 :=
  FiniteIntervals.of_fin 629800 200 complete_chunk3149

#print axioms interval_chunk3140
end Erdos184Work.PureFiveFilter4
