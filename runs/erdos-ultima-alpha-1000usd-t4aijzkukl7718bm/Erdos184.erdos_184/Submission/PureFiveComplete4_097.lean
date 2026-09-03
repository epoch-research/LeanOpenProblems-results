import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk970 : ∀ i : Fin 200, Compatible (194000 + i.val) →
    (table.lookup (194000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk970 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 194000 194200 :=
  FiniteIntervals.of_fin 194000 200 complete_chunk970

lemma complete_chunk971 : ∀ i : Fin 200, Compatible (194200 + i.val) →
    (table.lookup (194200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk971 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 194200 194400 :=
  FiniteIntervals.of_fin 194200 200 complete_chunk971

lemma complete_chunk972 : ∀ i : Fin 200, Compatible (194400 + i.val) →
    (table.lookup (194400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk972 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 194400 194600 :=
  FiniteIntervals.of_fin 194400 200 complete_chunk972

lemma complete_chunk973 : ∀ i : Fin 200, Compatible (194600 + i.val) →
    (table.lookup (194600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk973 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 194600 194800 :=
  FiniteIntervals.of_fin 194600 200 complete_chunk973

lemma complete_chunk974 : ∀ i : Fin 200, Compatible (194800 + i.val) →
    (table.lookup (194800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk974 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 194800 195000 :=
  FiniteIntervals.of_fin 194800 200 complete_chunk974

lemma complete_chunk975 : ∀ i : Fin 200, Compatible (195000 + i.val) →
    (table.lookup (195000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk975 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 195000 195200 :=
  FiniteIntervals.of_fin 195000 200 complete_chunk975

lemma complete_chunk976 : ∀ i : Fin 200, Compatible (195200 + i.val) →
    (table.lookup (195200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk976 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 195200 195400 :=
  FiniteIntervals.of_fin 195200 200 complete_chunk976

lemma complete_chunk977 : ∀ i : Fin 200, Compatible (195400 + i.val) →
    (table.lookup (195400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk977 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 195400 195600 :=
  FiniteIntervals.of_fin 195400 200 complete_chunk977

lemma complete_chunk978 : ∀ i : Fin 200, Compatible (195600 + i.val) →
    (table.lookup (195600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk978 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 195600 195800 :=
  FiniteIntervals.of_fin 195600 200 complete_chunk978

lemma complete_chunk979 : ∀ i : Fin 200, Compatible (195800 + i.val) →
    (table.lookup (195800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk979 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 195800 196000 :=
  FiniteIntervals.of_fin 195800 200 complete_chunk979

#print axioms interval_chunk970
end Erdos184Work.PureFiveFilter4
