import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk150 : ∀ i : Fin 200, Compatible (30000 + i.val) →
    (table.lookup (30000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk150 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 30000 30200 :=
  FiniteIntervals.of_fin 30000 200 complete_chunk150

lemma complete_chunk151 : ∀ i : Fin 200, Compatible (30200 + i.val) →
    (table.lookup (30200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk151 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 30200 30400 :=
  FiniteIntervals.of_fin 30200 200 complete_chunk151

lemma complete_chunk152 : ∀ i : Fin 200, Compatible (30400 + i.val) →
    (table.lookup (30400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk152 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 30400 30600 :=
  FiniteIntervals.of_fin 30400 200 complete_chunk152

lemma complete_chunk153 : ∀ i : Fin 200, Compatible (30600 + i.val) →
    (table.lookup (30600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk153 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 30600 30800 :=
  FiniteIntervals.of_fin 30600 200 complete_chunk153

lemma complete_chunk154 : ∀ i : Fin 200, Compatible (30800 + i.val) →
    (table.lookup (30800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk154 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 30800 31000 :=
  FiniteIntervals.of_fin 30800 200 complete_chunk154

lemma complete_chunk155 : ∀ i : Fin 200, Compatible (31000 + i.val) →
    (table.lookup (31000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk155 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 31000 31200 :=
  FiniteIntervals.of_fin 31000 200 complete_chunk155

lemma complete_chunk156 : ∀ i : Fin 200, Compatible (31200 + i.val) →
    (table.lookup (31200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk156 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 31200 31400 :=
  FiniteIntervals.of_fin 31200 200 complete_chunk156

lemma complete_chunk157 : ∀ i : Fin 200, Compatible (31400 + i.val) →
    (table.lookup (31400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk157 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 31400 31600 :=
  FiniteIntervals.of_fin 31400 200 complete_chunk157

lemma complete_chunk158 : ∀ i : Fin 200, Compatible (31600 + i.val) →
    (table.lookup (31600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk158 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 31600 31800 :=
  FiniteIntervals.of_fin 31600 200 complete_chunk158

lemma complete_chunk159 : ∀ i : Fin 200, Compatible (31800 + i.val) →
    (table.lookup (31800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk159 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 31800 32000 :=
  FiniteIntervals.of_fin 31800 200 complete_chunk159

#print axioms interval_chunk150
end Erdos184Work.PureFiveFilter3
