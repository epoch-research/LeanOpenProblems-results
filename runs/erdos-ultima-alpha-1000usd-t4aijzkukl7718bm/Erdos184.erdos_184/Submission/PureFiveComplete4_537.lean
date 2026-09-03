import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5370 : ∀ i : Fin 200, Compatible (1074000 + i.val) →
    (table.lookup (1074000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5370 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1074000 1074200 :=
  FiniteIntervals.of_fin 1074000 200 complete_chunk5370

lemma complete_chunk5371 : ∀ i : Fin 200, Compatible (1074200 + i.val) →
    (table.lookup (1074200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5371 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1074200 1074400 :=
  FiniteIntervals.of_fin 1074200 200 complete_chunk5371

lemma complete_chunk5372 : ∀ i : Fin 200, Compatible (1074400 + i.val) →
    (table.lookup (1074400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5372 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1074400 1074600 :=
  FiniteIntervals.of_fin 1074400 200 complete_chunk5372

lemma complete_chunk5373 : ∀ i : Fin 200, Compatible (1074600 + i.val) →
    (table.lookup (1074600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5373 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1074600 1074800 :=
  FiniteIntervals.of_fin 1074600 200 complete_chunk5373

lemma complete_chunk5374 : ∀ i : Fin 200, Compatible (1074800 + i.val) →
    (table.lookup (1074800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5374 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1074800 1075000 :=
  FiniteIntervals.of_fin 1074800 200 complete_chunk5374

lemma complete_chunk5375 : ∀ i : Fin 200, Compatible (1075000 + i.val) →
    (table.lookup (1075000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5375 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1075000 1075200 :=
  FiniteIntervals.of_fin 1075000 200 complete_chunk5375

lemma complete_chunk5376 : ∀ i : Fin 200, Compatible (1075200 + i.val) →
    (table.lookup (1075200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5376 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1075200 1075400 :=
  FiniteIntervals.of_fin 1075200 200 complete_chunk5376

lemma complete_chunk5377 : ∀ i : Fin 200, Compatible (1075400 + i.val) →
    (table.lookup (1075400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5377 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1075400 1075600 :=
  FiniteIntervals.of_fin 1075400 200 complete_chunk5377

lemma complete_chunk5378 : ∀ i : Fin 200, Compatible (1075600 + i.val) →
    (table.lookup (1075600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5378 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1075600 1075800 :=
  FiniteIntervals.of_fin 1075600 200 complete_chunk5378

lemma complete_chunk5379 : ∀ i : Fin 200, Compatible (1075800 + i.val) →
    (table.lookup (1075800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5379 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1075800 1076000 :=
  FiniteIntervals.of_fin 1075800 200 complete_chunk5379

#print axioms interval_chunk5370
end Erdos184Work.PureFiveFilter4
