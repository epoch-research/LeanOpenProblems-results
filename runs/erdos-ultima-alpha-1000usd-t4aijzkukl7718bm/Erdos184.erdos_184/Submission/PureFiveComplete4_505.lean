import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5050 : ∀ i : Fin 200, Compatible (1010000 + i.val) →
    (table.lookup (1010000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5050 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1010000 1010200 :=
  FiniteIntervals.of_fin 1010000 200 complete_chunk5050

lemma complete_chunk5051 : ∀ i : Fin 200, Compatible (1010200 + i.val) →
    (table.lookup (1010200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5051 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1010200 1010400 :=
  FiniteIntervals.of_fin 1010200 200 complete_chunk5051

lemma complete_chunk5052 : ∀ i : Fin 200, Compatible (1010400 + i.val) →
    (table.lookup (1010400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5052 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1010400 1010600 :=
  FiniteIntervals.of_fin 1010400 200 complete_chunk5052

lemma complete_chunk5053 : ∀ i : Fin 200, Compatible (1010600 + i.val) →
    (table.lookup (1010600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5053 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1010600 1010800 :=
  FiniteIntervals.of_fin 1010600 200 complete_chunk5053

lemma complete_chunk5054 : ∀ i : Fin 200, Compatible (1010800 + i.val) →
    (table.lookup (1010800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5054 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1010800 1011000 :=
  FiniteIntervals.of_fin 1010800 200 complete_chunk5054

lemma complete_chunk5055 : ∀ i : Fin 200, Compatible (1011000 + i.val) →
    (table.lookup (1011000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5055 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1011000 1011200 :=
  FiniteIntervals.of_fin 1011000 200 complete_chunk5055

lemma complete_chunk5056 : ∀ i : Fin 200, Compatible (1011200 + i.val) →
    (table.lookup (1011200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5056 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1011200 1011400 :=
  FiniteIntervals.of_fin 1011200 200 complete_chunk5056

lemma complete_chunk5057 : ∀ i : Fin 200, Compatible (1011400 + i.val) →
    (table.lookup (1011400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5057 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1011400 1011600 :=
  FiniteIntervals.of_fin 1011400 200 complete_chunk5057

lemma complete_chunk5058 : ∀ i : Fin 200, Compatible (1011600 + i.val) →
    (table.lookup (1011600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5058 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1011600 1011800 :=
  FiniteIntervals.of_fin 1011600 200 complete_chunk5058

lemma complete_chunk5059 : ∀ i : Fin 200, Compatible (1011800 + i.val) →
    (table.lookup (1011800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5059 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1011800 1012000 :=
  FiniteIntervals.of_fin 1011800 200 complete_chunk5059

#print axioms interval_chunk5050
end Erdos184Work.PureFiveFilter4
