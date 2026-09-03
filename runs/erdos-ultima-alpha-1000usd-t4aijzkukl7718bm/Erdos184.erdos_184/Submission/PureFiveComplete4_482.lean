import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4820 : ∀ i : Fin 200, Compatible (964000 + i.val) →
    (table.lookup (964000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4820 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 964000 964200 :=
  FiniteIntervals.of_fin 964000 200 complete_chunk4820

lemma complete_chunk4821 : ∀ i : Fin 200, Compatible (964200 + i.val) →
    (table.lookup (964200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4821 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 964200 964400 :=
  FiniteIntervals.of_fin 964200 200 complete_chunk4821

lemma complete_chunk4822 : ∀ i : Fin 200, Compatible (964400 + i.val) →
    (table.lookup (964400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4822 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 964400 964600 :=
  FiniteIntervals.of_fin 964400 200 complete_chunk4822

lemma complete_chunk4823 : ∀ i : Fin 200, Compatible (964600 + i.val) →
    (table.lookup (964600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4823 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 964600 964800 :=
  FiniteIntervals.of_fin 964600 200 complete_chunk4823

lemma complete_chunk4824 : ∀ i : Fin 200, Compatible (964800 + i.val) →
    (table.lookup (964800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4824 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 964800 965000 :=
  FiniteIntervals.of_fin 964800 200 complete_chunk4824

lemma complete_chunk4825 : ∀ i : Fin 200, Compatible (965000 + i.val) →
    (table.lookup (965000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4825 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 965000 965200 :=
  FiniteIntervals.of_fin 965000 200 complete_chunk4825

lemma complete_chunk4826 : ∀ i : Fin 200, Compatible (965200 + i.val) →
    (table.lookup (965200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4826 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 965200 965400 :=
  FiniteIntervals.of_fin 965200 200 complete_chunk4826

lemma complete_chunk4827 : ∀ i : Fin 200, Compatible (965400 + i.val) →
    (table.lookup (965400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4827 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 965400 965600 :=
  FiniteIntervals.of_fin 965400 200 complete_chunk4827

lemma complete_chunk4828 : ∀ i : Fin 200, Compatible (965600 + i.val) →
    (table.lookup (965600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4828 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 965600 965800 :=
  FiniteIntervals.of_fin 965600 200 complete_chunk4828

lemma complete_chunk4829 : ∀ i : Fin 200, Compatible (965800 + i.val) →
    (table.lookup (965800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4829 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 965800 966000 :=
  FiniteIntervals.of_fin 965800 200 complete_chunk4829

#print axioms interval_chunk4820
end Erdos184Work.PureFiveFilter4
