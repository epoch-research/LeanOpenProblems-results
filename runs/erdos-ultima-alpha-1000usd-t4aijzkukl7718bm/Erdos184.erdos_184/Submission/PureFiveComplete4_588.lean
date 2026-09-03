import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5880 : ∀ i : Fin 200, Compatible (1176000 + i.val) →
    (table.lookup (1176000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5880 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1176000 1176200 :=
  FiniteIntervals.of_fin 1176000 200 complete_chunk5880

lemma complete_chunk5881 : ∀ i : Fin 200, Compatible (1176200 + i.val) →
    (table.lookup (1176200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5881 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1176200 1176400 :=
  FiniteIntervals.of_fin 1176200 200 complete_chunk5881

lemma complete_chunk5882 : ∀ i : Fin 200, Compatible (1176400 + i.val) →
    (table.lookup (1176400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5882 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1176400 1176600 :=
  FiniteIntervals.of_fin 1176400 200 complete_chunk5882

lemma complete_chunk5883 : ∀ i : Fin 200, Compatible (1176600 + i.val) →
    (table.lookup (1176600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5883 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1176600 1176800 :=
  FiniteIntervals.of_fin 1176600 200 complete_chunk5883

lemma complete_chunk5884 : ∀ i : Fin 200, Compatible (1176800 + i.val) →
    (table.lookup (1176800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5884 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1176800 1177000 :=
  FiniteIntervals.of_fin 1176800 200 complete_chunk5884

lemma complete_chunk5885 : ∀ i : Fin 200, Compatible (1177000 + i.val) →
    (table.lookup (1177000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5885 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1177000 1177200 :=
  FiniteIntervals.of_fin 1177000 200 complete_chunk5885

lemma complete_chunk5886 : ∀ i : Fin 200, Compatible (1177200 + i.val) →
    (table.lookup (1177200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5886 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1177200 1177400 :=
  FiniteIntervals.of_fin 1177200 200 complete_chunk5886

lemma complete_chunk5887 : ∀ i : Fin 200, Compatible (1177400 + i.val) →
    (table.lookup (1177400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5887 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1177400 1177600 :=
  FiniteIntervals.of_fin 1177400 200 complete_chunk5887

lemma complete_chunk5888 : ∀ i : Fin 200, Compatible (1177600 + i.val) →
    (table.lookup (1177600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5888 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1177600 1177800 :=
  FiniteIntervals.of_fin 1177600 200 complete_chunk5888

lemma complete_chunk5889 : ∀ i : Fin 200, Compatible (1177800 + i.val) →
    (table.lookup (1177800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5889 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1177800 1178000 :=
  FiniteIntervals.of_fin 1177800 200 complete_chunk5889

#print axioms interval_chunk5880
end Erdos184Work.PureFiveFilter4
