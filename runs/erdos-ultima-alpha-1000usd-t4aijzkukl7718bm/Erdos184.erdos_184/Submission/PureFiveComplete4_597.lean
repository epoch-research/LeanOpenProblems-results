import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5970 : ∀ i : Fin 200, Compatible (1194000 + i.val) →
    (table.lookup (1194000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5970 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1194000 1194200 :=
  FiniteIntervals.of_fin 1194000 200 complete_chunk5970

lemma complete_chunk5971 : ∀ i : Fin 200, Compatible (1194200 + i.val) →
    (table.lookup (1194200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5971 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1194200 1194400 :=
  FiniteIntervals.of_fin 1194200 200 complete_chunk5971

lemma complete_chunk5972 : ∀ i : Fin 200, Compatible (1194400 + i.val) →
    (table.lookup (1194400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5972 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1194400 1194600 :=
  FiniteIntervals.of_fin 1194400 200 complete_chunk5972

lemma complete_chunk5973 : ∀ i : Fin 200, Compatible (1194600 + i.val) →
    (table.lookup (1194600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5973 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1194600 1194800 :=
  FiniteIntervals.of_fin 1194600 200 complete_chunk5973

lemma complete_chunk5974 : ∀ i : Fin 200, Compatible (1194800 + i.val) →
    (table.lookup (1194800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5974 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1194800 1195000 :=
  FiniteIntervals.of_fin 1194800 200 complete_chunk5974

lemma complete_chunk5975 : ∀ i : Fin 200, Compatible (1195000 + i.val) →
    (table.lookup (1195000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5975 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1195000 1195200 :=
  FiniteIntervals.of_fin 1195000 200 complete_chunk5975

lemma complete_chunk5976 : ∀ i : Fin 200, Compatible (1195200 + i.val) →
    (table.lookup (1195200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5976 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1195200 1195400 :=
  FiniteIntervals.of_fin 1195200 200 complete_chunk5976

lemma complete_chunk5977 : ∀ i : Fin 200, Compatible (1195400 + i.val) →
    (table.lookup (1195400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5977 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1195400 1195600 :=
  FiniteIntervals.of_fin 1195400 200 complete_chunk5977

lemma complete_chunk5978 : ∀ i : Fin 200, Compatible (1195600 + i.val) →
    (table.lookup (1195600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5978 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1195600 1195800 :=
  FiniteIntervals.of_fin 1195600 200 complete_chunk5978

lemma complete_chunk5979 : ∀ i : Fin 200, Compatible (1195800 + i.val) →
    (table.lookup (1195800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5979 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1195800 1196000 :=
  FiniteIntervals.of_fin 1195800 200 complete_chunk5979

#print axioms interval_chunk5970
end Erdos184Work.PureFiveFilter4
