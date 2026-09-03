import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3090 : ∀ i : Fin 200, Compatible (618000 + i.val) →
    (table.lookup (618000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3090 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 618000 618200 :=
  FiniteIntervals.of_fin 618000 200 complete_chunk3090

lemma complete_chunk3091 : ∀ i : Fin 200, Compatible (618200 + i.val) →
    (table.lookup (618200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3091 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 618200 618400 :=
  FiniteIntervals.of_fin 618200 200 complete_chunk3091

lemma complete_chunk3092 : ∀ i : Fin 200, Compatible (618400 + i.val) →
    (table.lookup (618400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3092 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 618400 618600 :=
  FiniteIntervals.of_fin 618400 200 complete_chunk3092

lemma complete_chunk3093 : ∀ i : Fin 200, Compatible (618600 + i.val) →
    (table.lookup (618600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3093 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 618600 618800 :=
  FiniteIntervals.of_fin 618600 200 complete_chunk3093

lemma complete_chunk3094 : ∀ i : Fin 200, Compatible (618800 + i.val) →
    (table.lookup (618800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3094 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 618800 619000 :=
  FiniteIntervals.of_fin 618800 200 complete_chunk3094

lemma complete_chunk3095 : ∀ i : Fin 200, Compatible (619000 + i.val) →
    (table.lookup (619000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3095 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 619000 619200 :=
  FiniteIntervals.of_fin 619000 200 complete_chunk3095

lemma complete_chunk3096 : ∀ i : Fin 200, Compatible (619200 + i.val) →
    (table.lookup (619200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3096 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 619200 619400 :=
  FiniteIntervals.of_fin 619200 200 complete_chunk3096

lemma complete_chunk3097 : ∀ i : Fin 200, Compatible (619400 + i.val) →
    (table.lookup (619400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3097 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 619400 619600 :=
  FiniteIntervals.of_fin 619400 200 complete_chunk3097

lemma complete_chunk3098 : ∀ i : Fin 200, Compatible (619600 + i.val) →
    (table.lookup (619600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3098 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 619600 619800 :=
  FiniteIntervals.of_fin 619600 200 complete_chunk3098

lemma complete_chunk3099 : ∀ i : Fin 200, Compatible (619800 + i.val) →
    (table.lookup (619800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3099 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 619800 620000 :=
  FiniteIntervals.of_fin 619800 200 complete_chunk3099

#print axioms interval_chunk3090
end Erdos184Work.PureFiveFilter4
