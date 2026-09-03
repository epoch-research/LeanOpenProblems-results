import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4620 : ∀ i : Fin 200, Compatible (924000 + i.val) →
    (table.lookup (924000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4620 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 924000 924200 :=
  FiniteIntervals.of_fin 924000 200 complete_chunk4620

lemma complete_chunk4621 : ∀ i : Fin 200, Compatible (924200 + i.val) →
    (table.lookup (924200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4621 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 924200 924400 :=
  FiniteIntervals.of_fin 924200 200 complete_chunk4621

lemma complete_chunk4622 : ∀ i : Fin 200, Compatible (924400 + i.val) →
    (table.lookup (924400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4622 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 924400 924600 :=
  FiniteIntervals.of_fin 924400 200 complete_chunk4622

lemma complete_chunk4623 : ∀ i : Fin 200, Compatible (924600 + i.val) →
    (table.lookup (924600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4623 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 924600 924800 :=
  FiniteIntervals.of_fin 924600 200 complete_chunk4623

lemma complete_chunk4624 : ∀ i : Fin 200, Compatible (924800 + i.val) →
    (table.lookup (924800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4624 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 924800 925000 :=
  FiniteIntervals.of_fin 924800 200 complete_chunk4624

lemma complete_chunk4625 : ∀ i : Fin 200, Compatible (925000 + i.val) →
    (table.lookup (925000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4625 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 925000 925200 :=
  FiniteIntervals.of_fin 925000 200 complete_chunk4625

lemma complete_chunk4626 : ∀ i : Fin 200, Compatible (925200 + i.val) →
    (table.lookup (925200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4626 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 925200 925400 :=
  FiniteIntervals.of_fin 925200 200 complete_chunk4626

lemma complete_chunk4627 : ∀ i : Fin 200, Compatible (925400 + i.val) →
    (table.lookup (925400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4627 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 925400 925600 :=
  FiniteIntervals.of_fin 925400 200 complete_chunk4627

lemma complete_chunk4628 : ∀ i : Fin 200, Compatible (925600 + i.val) →
    (table.lookup (925600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4628 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 925600 925800 :=
  FiniteIntervals.of_fin 925600 200 complete_chunk4628

lemma complete_chunk4629 : ∀ i : Fin 200, Compatible (925800 + i.val) →
    (table.lookup (925800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4629 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 925800 926000 :=
  FiniteIntervals.of_fin 925800 200 complete_chunk4629

#print axioms interval_chunk4620
end Erdos184Work.PureFiveFilter4
