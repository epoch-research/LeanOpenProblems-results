import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3980 : ∀ i : Fin 200, Compatible (796000 + i.val) →
    (table.lookup (796000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3980 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 796000 796200 :=
  FiniteIntervals.of_fin 796000 200 complete_chunk3980

lemma complete_chunk3981 : ∀ i : Fin 200, Compatible (796200 + i.val) →
    (table.lookup (796200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3981 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 796200 796400 :=
  FiniteIntervals.of_fin 796200 200 complete_chunk3981

lemma complete_chunk3982 : ∀ i : Fin 200, Compatible (796400 + i.val) →
    (table.lookup (796400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3982 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 796400 796600 :=
  FiniteIntervals.of_fin 796400 200 complete_chunk3982

lemma complete_chunk3983 : ∀ i : Fin 200, Compatible (796600 + i.val) →
    (table.lookup (796600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3983 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 796600 796800 :=
  FiniteIntervals.of_fin 796600 200 complete_chunk3983

lemma complete_chunk3984 : ∀ i : Fin 200, Compatible (796800 + i.val) →
    (table.lookup (796800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3984 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 796800 797000 :=
  FiniteIntervals.of_fin 796800 200 complete_chunk3984

lemma complete_chunk3985 : ∀ i : Fin 200, Compatible (797000 + i.val) →
    (table.lookup (797000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3985 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 797000 797200 :=
  FiniteIntervals.of_fin 797000 200 complete_chunk3985

lemma complete_chunk3986 : ∀ i : Fin 200, Compatible (797200 + i.val) →
    (table.lookup (797200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3986 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 797200 797400 :=
  FiniteIntervals.of_fin 797200 200 complete_chunk3986

lemma complete_chunk3987 : ∀ i : Fin 200, Compatible (797400 + i.val) →
    (table.lookup (797400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3987 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 797400 797600 :=
  FiniteIntervals.of_fin 797400 200 complete_chunk3987

lemma complete_chunk3988 : ∀ i : Fin 200, Compatible (797600 + i.val) →
    (table.lookup (797600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3988 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 797600 797800 :=
  FiniteIntervals.of_fin 797600 200 complete_chunk3988

lemma complete_chunk3989 : ∀ i : Fin 200, Compatible (797800 + i.val) →
    (table.lookup (797800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3989 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 797800 798000 :=
  FiniteIntervals.of_fin 797800 200 complete_chunk3989

#print axioms interval_chunk3980
end Erdos184Work.PureFiveFilter4
