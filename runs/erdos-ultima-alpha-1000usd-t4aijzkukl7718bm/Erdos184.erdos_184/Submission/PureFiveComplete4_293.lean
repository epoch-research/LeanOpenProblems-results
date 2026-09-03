import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2930 : ∀ i : Fin 200, Compatible (586000 + i.val) →
    (table.lookup (586000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2930 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 586000 586200 :=
  FiniteIntervals.of_fin 586000 200 complete_chunk2930

lemma complete_chunk2931 : ∀ i : Fin 200, Compatible (586200 + i.val) →
    (table.lookup (586200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2931 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 586200 586400 :=
  FiniteIntervals.of_fin 586200 200 complete_chunk2931

lemma complete_chunk2932 : ∀ i : Fin 200, Compatible (586400 + i.val) →
    (table.lookup (586400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2932 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 586400 586600 :=
  FiniteIntervals.of_fin 586400 200 complete_chunk2932

lemma complete_chunk2933 : ∀ i : Fin 200, Compatible (586600 + i.val) →
    (table.lookup (586600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2933 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 586600 586800 :=
  FiniteIntervals.of_fin 586600 200 complete_chunk2933

lemma complete_chunk2934 : ∀ i : Fin 200, Compatible (586800 + i.val) →
    (table.lookup (586800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2934 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 586800 587000 :=
  FiniteIntervals.of_fin 586800 200 complete_chunk2934

lemma complete_chunk2935 : ∀ i : Fin 200, Compatible (587000 + i.val) →
    (table.lookup (587000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2935 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 587000 587200 :=
  FiniteIntervals.of_fin 587000 200 complete_chunk2935

lemma complete_chunk2936 : ∀ i : Fin 200, Compatible (587200 + i.val) →
    (table.lookup (587200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2936 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 587200 587400 :=
  FiniteIntervals.of_fin 587200 200 complete_chunk2936

lemma complete_chunk2937 : ∀ i : Fin 200, Compatible (587400 + i.val) →
    (table.lookup (587400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2937 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 587400 587600 :=
  FiniteIntervals.of_fin 587400 200 complete_chunk2937

lemma complete_chunk2938 : ∀ i : Fin 200, Compatible (587600 + i.val) →
    (table.lookup (587600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2938 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 587600 587800 :=
  FiniteIntervals.of_fin 587600 200 complete_chunk2938

lemma complete_chunk2939 : ∀ i : Fin 200, Compatible (587800 + i.val) →
    (table.lookup (587800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2939 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 587800 588000 :=
  FiniteIntervals.of_fin 587800 200 complete_chunk2939

#print axioms interval_chunk2930
end Erdos184Work.PureFiveFilter4
