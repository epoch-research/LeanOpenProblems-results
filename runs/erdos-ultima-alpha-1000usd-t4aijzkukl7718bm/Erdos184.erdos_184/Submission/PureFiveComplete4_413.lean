import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4130 : ∀ i : Fin 200, Compatible (826000 + i.val) →
    (table.lookup (826000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4130 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 826000 826200 :=
  FiniteIntervals.of_fin 826000 200 complete_chunk4130

lemma complete_chunk4131 : ∀ i : Fin 200, Compatible (826200 + i.val) →
    (table.lookup (826200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4131 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 826200 826400 :=
  FiniteIntervals.of_fin 826200 200 complete_chunk4131

lemma complete_chunk4132 : ∀ i : Fin 200, Compatible (826400 + i.val) →
    (table.lookup (826400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4132 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 826400 826600 :=
  FiniteIntervals.of_fin 826400 200 complete_chunk4132

lemma complete_chunk4133 : ∀ i : Fin 200, Compatible (826600 + i.val) →
    (table.lookup (826600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4133 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 826600 826800 :=
  FiniteIntervals.of_fin 826600 200 complete_chunk4133

lemma complete_chunk4134 : ∀ i : Fin 200, Compatible (826800 + i.val) →
    (table.lookup (826800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4134 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 826800 827000 :=
  FiniteIntervals.of_fin 826800 200 complete_chunk4134

lemma complete_chunk4135 : ∀ i : Fin 200, Compatible (827000 + i.val) →
    (table.lookup (827000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4135 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 827000 827200 :=
  FiniteIntervals.of_fin 827000 200 complete_chunk4135

lemma complete_chunk4136 : ∀ i : Fin 200, Compatible (827200 + i.val) →
    (table.lookup (827200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4136 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 827200 827400 :=
  FiniteIntervals.of_fin 827200 200 complete_chunk4136

lemma complete_chunk4137 : ∀ i : Fin 200, Compatible (827400 + i.val) →
    (table.lookup (827400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4137 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 827400 827600 :=
  FiniteIntervals.of_fin 827400 200 complete_chunk4137

lemma complete_chunk4138 : ∀ i : Fin 200, Compatible (827600 + i.val) →
    (table.lookup (827600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4138 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 827600 827800 :=
  FiniteIntervals.of_fin 827600 200 complete_chunk4138

lemma complete_chunk4139 : ∀ i : Fin 200, Compatible (827800 + i.val) →
    (table.lookup (827800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4139 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 827800 828000 :=
  FiniteIntervals.of_fin 827800 200 complete_chunk4139

#print axioms interval_chunk4130
end Erdos184Work.PureFiveFilter4
