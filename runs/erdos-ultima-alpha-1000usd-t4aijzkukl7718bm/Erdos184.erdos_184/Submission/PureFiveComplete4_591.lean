import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5910 : ∀ i : Fin 200, Compatible (1182000 + i.val) →
    (table.lookup (1182000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5910 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1182000 1182200 :=
  FiniteIntervals.of_fin 1182000 200 complete_chunk5910

lemma complete_chunk5911 : ∀ i : Fin 200, Compatible (1182200 + i.val) →
    (table.lookup (1182200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5911 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1182200 1182400 :=
  FiniteIntervals.of_fin 1182200 200 complete_chunk5911

lemma complete_chunk5912 : ∀ i : Fin 200, Compatible (1182400 + i.val) →
    (table.lookup (1182400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5912 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1182400 1182600 :=
  FiniteIntervals.of_fin 1182400 200 complete_chunk5912

lemma complete_chunk5913 : ∀ i : Fin 200, Compatible (1182600 + i.val) →
    (table.lookup (1182600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5913 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1182600 1182800 :=
  FiniteIntervals.of_fin 1182600 200 complete_chunk5913

lemma complete_chunk5914 : ∀ i : Fin 200, Compatible (1182800 + i.val) →
    (table.lookup (1182800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5914 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1182800 1183000 :=
  FiniteIntervals.of_fin 1182800 200 complete_chunk5914

lemma complete_chunk5915 : ∀ i : Fin 200, Compatible (1183000 + i.val) →
    (table.lookup (1183000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5915 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1183000 1183200 :=
  FiniteIntervals.of_fin 1183000 200 complete_chunk5915

lemma complete_chunk5916 : ∀ i : Fin 200, Compatible (1183200 + i.val) →
    (table.lookup (1183200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5916 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1183200 1183400 :=
  FiniteIntervals.of_fin 1183200 200 complete_chunk5916

lemma complete_chunk5917 : ∀ i : Fin 200, Compatible (1183400 + i.val) →
    (table.lookup (1183400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5917 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1183400 1183600 :=
  FiniteIntervals.of_fin 1183400 200 complete_chunk5917

lemma complete_chunk5918 : ∀ i : Fin 200, Compatible (1183600 + i.val) →
    (table.lookup (1183600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5918 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1183600 1183800 :=
  FiniteIntervals.of_fin 1183600 200 complete_chunk5918

lemma complete_chunk5919 : ∀ i : Fin 200, Compatible (1183800 + i.val) →
    (table.lookup (1183800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5919 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1183800 1184000 :=
  FiniteIntervals.of_fin 1183800 200 complete_chunk5919

#print axioms interval_chunk5910
end Erdos184Work.PureFiveFilter4
