import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2980 : ∀ i : Fin 200, Compatible (596000 + i.val) →
    (table.lookup (596000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2980 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 596000 596200 :=
  FiniteIntervals.of_fin 596000 200 complete_chunk2980

lemma complete_chunk2981 : ∀ i : Fin 200, Compatible (596200 + i.val) →
    (table.lookup (596200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2981 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 596200 596400 :=
  FiniteIntervals.of_fin 596200 200 complete_chunk2981

lemma complete_chunk2982 : ∀ i : Fin 200, Compatible (596400 + i.val) →
    (table.lookup (596400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2982 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 596400 596600 :=
  FiniteIntervals.of_fin 596400 200 complete_chunk2982

lemma complete_chunk2983 : ∀ i : Fin 200, Compatible (596600 + i.val) →
    (table.lookup (596600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2983 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 596600 596800 :=
  FiniteIntervals.of_fin 596600 200 complete_chunk2983

lemma complete_chunk2984 : ∀ i : Fin 200, Compatible (596800 + i.val) →
    (table.lookup (596800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2984 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 596800 597000 :=
  FiniteIntervals.of_fin 596800 200 complete_chunk2984

lemma complete_chunk2985 : ∀ i : Fin 200, Compatible (597000 + i.val) →
    (table.lookup (597000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2985 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 597000 597200 :=
  FiniteIntervals.of_fin 597000 200 complete_chunk2985

lemma complete_chunk2986 : ∀ i : Fin 200, Compatible (597200 + i.val) →
    (table.lookup (597200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2986 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 597200 597400 :=
  FiniteIntervals.of_fin 597200 200 complete_chunk2986

lemma complete_chunk2987 : ∀ i : Fin 200, Compatible (597400 + i.val) →
    (table.lookup (597400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2987 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 597400 597600 :=
  FiniteIntervals.of_fin 597400 200 complete_chunk2987

lemma complete_chunk2988 : ∀ i : Fin 200, Compatible (597600 + i.val) →
    (table.lookup (597600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2988 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 597600 597800 :=
  FiniteIntervals.of_fin 597600 200 complete_chunk2988

lemma complete_chunk2989 : ∀ i : Fin 200, Compatible (597800 + i.val) →
    (table.lookup (597800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2989 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 597800 598000 :=
  FiniteIntervals.of_fin 597800 200 complete_chunk2989

#print axioms interval_chunk2980
end Erdos184Work.PureFiveFilter4
