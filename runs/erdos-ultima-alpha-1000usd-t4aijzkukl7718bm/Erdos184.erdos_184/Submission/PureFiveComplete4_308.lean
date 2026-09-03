import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3080 : ∀ i : Fin 200, Compatible (616000 + i.val) →
    (table.lookup (616000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3080 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 616000 616200 :=
  FiniteIntervals.of_fin 616000 200 complete_chunk3080

lemma complete_chunk3081 : ∀ i : Fin 200, Compatible (616200 + i.val) →
    (table.lookup (616200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3081 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 616200 616400 :=
  FiniteIntervals.of_fin 616200 200 complete_chunk3081

lemma complete_chunk3082 : ∀ i : Fin 200, Compatible (616400 + i.val) →
    (table.lookup (616400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3082 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 616400 616600 :=
  FiniteIntervals.of_fin 616400 200 complete_chunk3082

lemma complete_chunk3083 : ∀ i : Fin 200, Compatible (616600 + i.val) →
    (table.lookup (616600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3083 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 616600 616800 :=
  FiniteIntervals.of_fin 616600 200 complete_chunk3083

lemma complete_chunk3084 : ∀ i : Fin 200, Compatible (616800 + i.val) →
    (table.lookup (616800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3084 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 616800 617000 :=
  FiniteIntervals.of_fin 616800 200 complete_chunk3084

lemma complete_chunk3085 : ∀ i : Fin 200, Compatible (617000 + i.val) →
    (table.lookup (617000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3085 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 617000 617200 :=
  FiniteIntervals.of_fin 617000 200 complete_chunk3085

lemma complete_chunk3086 : ∀ i : Fin 200, Compatible (617200 + i.val) →
    (table.lookup (617200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3086 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 617200 617400 :=
  FiniteIntervals.of_fin 617200 200 complete_chunk3086

lemma complete_chunk3087 : ∀ i : Fin 200, Compatible (617400 + i.val) →
    (table.lookup (617400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3087 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 617400 617600 :=
  FiniteIntervals.of_fin 617400 200 complete_chunk3087

lemma complete_chunk3088 : ∀ i : Fin 200, Compatible (617600 + i.val) →
    (table.lookup (617600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3088 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 617600 617800 :=
  FiniteIntervals.of_fin 617600 200 complete_chunk3088

lemma complete_chunk3089 : ∀ i : Fin 200, Compatible (617800 + i.val) →
    (table.lookup (617800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3089 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 617800 618000 :=
  FiniteIntervals.of_fin 617800 200 complete_chunk3089

#print axioms interval_chunk3080
end Erdos184Work.PureFiveFilter4
