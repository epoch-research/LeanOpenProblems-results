import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4630 : ∀ i : Fin 200, Compatible (926000 + i.val) →
    (table.lookup (926000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4630 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 926000 926200 :=
  FiniteIntervals.of_fin 926000 200 complete_chunk4630

lemma complete_chunk4631 : ∀ i : Fin 200, Compatible (926200 + i.val) →
    (table.lookup (926200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4631 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 926200 926400 :=
  FiniteIntervals.of_fin 926200 200 complete_chunk4631

lemma complete_chunk4632 : ∀ i : Fin 200, Compatible (926400 + i.val) →
    (table.lookup (926400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4632 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 926400 926600 :=
  FiniteIntervals.of_fin 926400 200 complete_chunk4632

lemma complete_chunk4633 : ∀ i : Fin 200, Compatible (926600 + i.val) →
    (table.lookup (926600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4633 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 926600 926800 :=
  FiniteIntervals.of_fin 926600 200 complete_chunk4633

lemma complete_chunk4634 : ∀ i : Fin 200, Compatible (926800 + i.val) →
    (table.lookup (926800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4634 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 926800 927000 :=
  FiniteIntervals.of_fin 926800 200 complete_chunk4634

lemma complete_chunk4635 : ∀ i : Fin 200, Compatible (927000 + i.val) →
    (table.lookup (927000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4635 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 927000 927200 :=
  FiniteIntervals.of_fin 927000 200 complete_chunk4635

lemma complete_chunk4636 : ∀ i : Fin 200, Compatible (927200 + i.val) →
    (table.lookup (927200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4636 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 927200 927400 :=
  FiniteIntervals.of_fin 927200 200 complete_chunk4636

lemma complete_chunk4637 : ∀ i : Fin 200, Compatible (927400 + i.val) →
    (table.lookup (927400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4637 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 927400 927600 :=
  FiniteIntervals.of_fin 927400 200 complete_chunk4637

lemma complete_chunk4638 : ∀ i : Fin 200, Compatible (927600 + i.val) →
    (table.lookup (927600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4638 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 927600 927800 :=
  FiniteIntervals.of_fin 927600 200 complete_chunk4638

lemma complete_chunk4639 : ∀ i : Fin 200, Compatible (927800 + i.val) →
    (table.lookup (927800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4639 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 927800 928000 :=
  FiniteIntervals.of_fin 927800 200 complete_chunk4639

#print axioms interval_chunk4630
end Erdos184Work.PureFiveFilter4
