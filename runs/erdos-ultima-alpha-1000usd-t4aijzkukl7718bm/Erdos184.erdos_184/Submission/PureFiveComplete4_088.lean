import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk880 : ∀ i : Fin 200, Compatible (176000 + i.val) →
    (table.lookup (176000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk880 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 176000 176200 :=
  FiniteIntervals.of_fin 176000 200 complete_chunk880

lemma complete_chunk881 : ∀ i : Fin 200, Compatible (176200 + i.val) →
    (table.lookup (176200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk881 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 176200 176400 :=
  FiniteIntervals.of_fin 176200 200 complete_chunk881

lemma complete_chunk882 : ∀ i : Fin 200, Compatible (176400 + i.val) →
    (table.lookup (176400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk882 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 176400 176600 :=
  FiniteIntervals.of_fin 176400 200 complete_chunk882

lemma complete_chunk883 : ∀ i : Fin 200, Compatible (176600 + i.val) →
    (table.lookup (176600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk883 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 176600 176800 :=
  FiniteIntervals.of_fin 176600 200 complete_chunk883

lemma complete_chunk884 : ∀ i : Fin 200, Compatible (176800 + i.val) →
    (table.lookup (176800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk884 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 176800 177000 :=
  FiniteIntervals.of_fin 176800 200 complete_chunk884

lemma complete_chunk885 : ∀ i : Fin 200, Compatible (177000 + i.val) →
    (table.lookup (177000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk885 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 177000 177200 :=
  FiniteIntervals.of_fin 177000 200 complete_chunk885

lemma complete_chunk886 : ∀ i : Fin 200, Compatible (177200 + i.val) →
    (table.lookup (177200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk886 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 177200 177400 :=
  FiniteIntervals.of_fin 177200 200 complete_chunk886

lemma complete_chunk887 : ∀ i : Fin 200, Compatible (177400 + i.val) →
    (table.lookup (177400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk887 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 177400 177600 :=
  FiniteIntervals.of_fin 177400 200 complete_chunk887

lemma complete_chunk888 : ∀ i : Fin 200, Compatible (177600 + i.val) →
    (table.lookup (177600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk888 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 177600 177800 :=
  FiniteIntervals.of_fin 177600 200 complete_chunk888

lemma complete_chunk889 : ∀ i : Fin 200, Compatible (177800 + i.val) →
    (table.lookup (177800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk889 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 177800 178000 :=
  FiniteIntervals.of_fin 177800 200 complete_chunk889

#print axioms interval_chunk880
end Erdos184Work.PureFiveFilter4
