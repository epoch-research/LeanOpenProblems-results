import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3840 : ∀ i : Fin 200, Compatible (768000 + i.val) →
    (table.lookup (768000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3840 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 768000 768200 :=
  FiniteIntervals.of_fin 768000 200 complete_chunk3840

lemma complete_chunk3841 : ∀ i : Fin 200, Compatible (768200 + i.val) →
    (table.lookup (768200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3841 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 768200 768400 :=
  FiniteIntervals.of_fin 768200 200 complete_chunk3841

lemma complete_chunk3842 : ∀ i : Fin 200, Compatible (768400 + i.val) →
    (table.lookup (768400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3842 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 768400 768600 :=
  FiniteIntervals.of_fin 768400 200 complete_chunk3842

lemma complete_chunk3843 : ∀ i : Fin 200, Compatible (768600 + i.val) →
    (table.lookup (768600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3843 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 768600 768800 :=
  FiniteIntervals.of_fin 768600 200 complete_chunk3843

lemma complete_chunk3844 : ∀ i : Fin 200, Compatible (768800 + i.val) →
    (table.lookup (768800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3844 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 768800 769000 :=
  FiniteIntervals.of_fin 768800 200 complete_chunk3844

lemma complete_chunk3845 : ∀ i : Fin 200, Compatible (769000 + i.val) →
    (table.lookup (769000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3845 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 769000 769200 :=
  FiniteIntervals.of_fin 769000 200 complete_chunk3845

lemma complete_chunk3846 : ∀ i : Fin 200, Compatible (769200 + i.val) →
    (table.lookup (769200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3846 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 769200 769400 :=
  FiniteIntervals.of_fin 769200 200 complete_chunk3846

lemma complete_chunk3847 : ∀ i : Fin 200, Compatible (769400 + i.val) →
    (table.lookup (769400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3847 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 769400 769600 :=
  FiniteIntervals.of_fin 769400 200 complete_chunk3847

lemma complete_chunk3848 : ∀ i : Fin 200, Compatible (769600 + i.val) →
    (table.lookup (769600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3848 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 769600 769800 :=
  FiniteIntervals.of_fin 769600 200 complete_chunk3848

lemma complete_chunk3849 : ∀ i : Fin 200, Compatible (769800 + i.val) →
    (table.lookup (769800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3849 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 769800 770000 :=
  FiniteIntervals.of_fin 769800 200 complete_chunk3849

#print axioms interval_chunk3840
end Erdos184Work.PureFiveFilter4
