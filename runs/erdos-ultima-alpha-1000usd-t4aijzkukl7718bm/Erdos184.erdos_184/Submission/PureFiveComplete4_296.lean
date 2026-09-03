import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2960 : ∀ i : Fin 200, Compatible (592000 + i.val) →
    (table.lookup (592000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2960 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 592000 592200 :=
  FiniteIntervals.of_fin 592000 200 complete_chunk2960

lemma complete_chunk2961 : ∀ i : Fin 200, Compatible (592200 + i.val) →
    (table.lookup (592200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2961 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 592200 592400 :=
  FiniteIntervals.of_fin 592200 200 complete_chunk2961

lemma complete_chunk2962 : ∀ i : Fin 200, Compatible (592400 + i.val) →
    (table.lookup (592400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2962 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 592400 592600 :=
  FiniteIntervals.of_fin 592400 200 complete_chunk2962

lemma complete_chunk2963 : ∀ i : Fin 200, Compatible (592600 + i.val) →
    (table.lookup (592600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2963 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 592600 592800 :=
  FiniteIntervals.of_fin 592600 200 complete_chunk2963

lemma complete_chunk2964 : ∀ i : Fin 200, Compatible (592800 + i.val) →
    (table.lookup (592800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2964 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 592800 593000 :=
  FiniteIntervals.of_fin 592800 200 complete_chunk2964

lemma complete_chunk2965 : ∀ i : Fin 200, Compatible (593000 + i.val) →
    (table.lookup (593000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2965 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 593000 593200 :=
  FiniteIntervals.of_fin 593000 200 complete_chunk2965

lemma complete_chunk2966 : ∀ i : Fin 200, Compatible (593200 + i.val) →
    (table.lookup (593200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2966 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 593200 593400 :=
  FiniteIntervals.of_fin 593200 200 complete_chunk2966

lemma complete_chunk2967 : ∀ i : Fin 200, Compatible (593400 + i.val) →
    (table.lookup (593400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2967 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 593400 593600 :=
  FiniteIntervals.of_fin 593400 200 complete_chunk2967

lemma complete_chunk2968 : ∀ i : Fin 200, Compatible (593600 + i.val) →
    (table.lookup (593600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2968 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 593600 593800 :=
  FiniteIntervals.of_fin 593600 200 complete_chunk2968

lemma complete_chunk2969 : ∀ i : Fin 200, Compatible (593800 + i.val) →
    (table.lookup (593800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2969 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 593800 594000 :=
  FiniteIntervals.of_fin 593800 200 complete_chunk2969

#print axioms interval_chunk2960
end Erdos184Work.PureFiveFilter4
