import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk910 : ∀ i : Fin 200, Compatible (182000 + i.val) →
    (table.lookup (182000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk910 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 182000 182200 :=
  FiniteIntervals.of_fin 182000 200 complete_chunk910

lemma complete_chunk911 : ∀ i : Fin 200, Compatible (182200 + i.val) →
    (table.lookup (182200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk911 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 182200 182400 :=
  FiniteIntervals.of_fin 182200 200 complete_chunk911

lemma complete_chunk912 : ∀ i : Fin 200, Compatible (182400 + i.val) →
    (table.lookup (182400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk912 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 182400 182600 :=
  FiniteIntervals.of_fin 182400 200 complete_chunk912

lemma complete_chunk913 : ∀ i : Fin 200, Compatible (182600 + i.val) →
    (table.lookup (182600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk913 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 182600 182800 :=
  FiniteIntervals.of_fin 182600 200 complete_chunk913

lemma complete_chunk914 : ∀ i : Fin 200, Compatible (182800 + i.val) →
    (table.lookup (182800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk914 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 182800 183000 :=
  FiniteIntervals.of_fin 182800 200 complete_chunk914

lemma complete_chunk915 : ∀ i : Fin 200, Compatible (183000 + i.val) →
    (table.lookup (183000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk915 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 183000 183200 :=
  FiniteIntervals.of_fin 183000 200 complete_chunk915

lemma complete_chunk916 : ∀ i : Fin 200, Compatible (183200 + i.val) →
    (table.lookup (183200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk916 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 183200 183400 :=
  FiniteIntervals.of_fin 183200 200 complete_chunk916

lemma complete_chunk917 : ∀ i : Fin 200, Compatible (183400 + i.val) →
    (table.lookup (183400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk917 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 183400 183600 :=
  FiniteIntervals.of_fin 183400 200 complete_chunk917

lemma complete_chunk918 : ∀ i : Fin 200, Compatible (183600 + i.val) →
    (table.lookup (183600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk918 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 183600 183800 :=
  FiniteIntervals.of_fin 183600 200 complete_chunk918

lemma complete_chunk919 : ∀ i : Fin 200, Compatible (183800 + i.val) →
    (table.lookup (183800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk919 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 183800 184000 :=
  FiniteIntervals.of_fin 183800 200 complete_chunk919

#print axioms interval_chunk910
end Erdos184Work.PureFiveFilter4
