import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3930 : ∀ i : Fin 200, Compatible (786000 + i.val) →
    (table.lookup (786000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3930 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 786000 786200 :=
  FiniteIntervals.of_fin 786000 200 complete_chunk3930

lemma complete_chunk3931 : ∀ i : Fin 200, Compatible (786200 + i.val) →
    (table.lookup (786200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3931 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 786200 786400 :=
  FiniteIntervals.of_fin 786200 200 complete_chunk3931

lemma complete_chunk3932 : ∀ i : Fin 200, Compatible (786400 + i.val) →
    (table.lookup (786400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3932 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 786400 786600 :=
  FiniteIntervals.of_fin 786400 200 complete_chunk3932

lemma complete_chunk3933 : ∀ i : Fin 200, Compatible (786600 + i.val) →
    (table.lookup (786600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3933 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 786600 786800 :=
  FiniteIntervals.of_fin 786600 200 complete_chunk3933

lemma complete_chunk3934 : ∀ i : Fin 200, Compatible (786800 + i.val) →
    (table.lookup (786800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3934 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 786800 787000 :=
  FiniteIntervals.of_fin 786800 200 complete_chunk3934

lemma complete_chunk3935 : ∀ i : Fin 200, Compatible (787000 + i.val) →
    (table.lookup (787000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3935 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 787000 787200 :=
  FiniteIntervals.of_fin 787000 200 complete_chunk3935

lemma complete_chunk3936 : ∀ i : Fin 200, Compatible (787200 + i.val) →
    (table.lookup (787200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3936 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 787200 787400 :=
  FiniteIntervals.of_fin 787200 200 complete_chunk3936

lemma complete_chunk3937 : ∀ i : Fin 200, Compatible (787400 + i.val) →
    (table.lookup (787400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3937 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 787400 787600 :=
  FiniteIntervals.of_fin 787400 200 complete_chunk3937

lemma complete_chunk3938 : ∀ i : Fin 200, Compatible (787600 + i.val) →
    (table.lookup (787600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3938 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 787600 787800 :=
  FiniteIntervals.of_fin 787600 200 complete_chunk3938

lemma complete_chunk3939 : ∀ i : Fin 200, Compatible (787800 + i.val) →
    (table.lookup (787800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3939 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 787800 788000 :=
  FiniteIntervals.of_fin 787800 200 complete_chunk3939

#print axioms interval_chunk3930
end Erdos184Work.PureFiveFilter4
