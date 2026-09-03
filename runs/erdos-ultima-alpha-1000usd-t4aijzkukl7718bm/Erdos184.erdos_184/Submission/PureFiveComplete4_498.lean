import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4980 : ∀ i : Fin 200, Compatible (996000 + i.val) →
    (table.lookup (996000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4980 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 996000 996200 :=
  FiniteIntervals.of_fin 996000 200 complete_chunk4980

lemma complete_chunk4981 : ∀ i : Fin 200, Compatible (996200 + i.val) →
    (table.lookup (996200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4981 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 996200 996400 :=
  FiniteIntervals.of_fin 996200 200 complete_chunk4981

lemma complete_chunk4982 : ∀ i : Fin 200, Compatible (996400 + i.val) →
    (table.lookup (996400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4982 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 996400 996600 :=
  FiniteIntervals.of_fin 996400 200 complete_chunk4982

lemma complete_chunk4983 : ∀ i : Fin 200, Compatible (996600 + i.val) →
    (table.lookup (996600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4983 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 996600 996800 :=
  FiniteIntervals.of_fin 996600 200 complete_chunk4983

lemma complete_chunk4984 : ∀ i : Fin 200, Compatible (996800 + i.val) →
    (table.lookup (996800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4984 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 996800 997000 :=
  FiniteIntervals.of_fin 996800 200 complete_chunk4984

lemma complete_chunk4985 : ∀ i : Fin 200, Compatible (997000 + i.val) →
    (table.lookup (997000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4985 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 997000 997200 :=
  FiniteIntervals.of_fin 997000 200 complete_chunk4985

lemma complete_chunk4986 : ∀ i : Fin 200, Compatible (997200 + i.val) →
    (table.lookup (997200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4986 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 997200 997400 :=
  FiniteIntervals.of_fin 997200 200 complete_chunk4986

lemma complete_chunk4987 : ∀ i : Fin 200, Compatible (997400 + i.val) →
    (table.lookup (997400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4987 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 997400 997600 :=
  FiniteIntervals.of_fin 997400 200 complete_chunk4987

lemma complete_chunk4988 : ∀ i : Fin 200, Compatible (997600 + i.val) →
    (table.lookup (997600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4988 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 997600 997800 :=
  FiniteIntervals.of_fin 997600 200 complete_chunk4988

lemma complete_chunk4989 : ∀ i : Fin 200, Compatible (997800 + i.val) →
    (table.lookup (997800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4989 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 997800 998000 :=
  FiniteIntervals.of_fin 997800 200 complete_chunk4989

#print axioms interval_chunk4980
end Erdos184Work.PureFiveFilter4
