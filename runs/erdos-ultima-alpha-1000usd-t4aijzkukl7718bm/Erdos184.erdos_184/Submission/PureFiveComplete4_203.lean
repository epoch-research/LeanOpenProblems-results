import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2030 : ∀ i : Fin 200, Compatible (406000 + i.val) →
    (table.lookup (406000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2030 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 406000 406200 :=
  FiniteIntervals.of_fin 406000 200 complete_chunk2030

lemma complete_chunk2031 : ∀ i : Fin 200, Compatible (406200 + i.val) →
    (table.lookup (406200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2031 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 406200 406400 :=
  FiniteIntervals.of_fin 406200 200 complete_chunk2031

lemma complete_chunk2032 : ∀ i : Fin 200, Compatible (406400 + i.val) →
    (table.lookup (406400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2032 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 406400 406600 :=
  FiniteIntervals.of_fin 406400 200 complete_chunk2032

lemma complete_chunk2033 : ∀ i : Fin 200, Compatible (406600 + i.val) →
    (table.lookup (406600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2033 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 406600 406800 :=
  FiniteIntervals.of_fin 406600 200 complete_chunk2033

lemma complete_chunk2034 : ∀ i : Fin 200, Compatible (406800 + i.val) →
    (table.lookup (406800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2034 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 406800 407000 :=
  FiniteIntervals.of_fin 406800 200 complete_chunk2034

lemma complete_chunk2035 : ∀ i : Fin 200, Compatible (407000 + i.val) →
    (table.lookup (407000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2035 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 407000 407200 :=
  FiniteIntervals.of_fin 407000 200 complete_chunk2035

lemma complete_chunk2036 : ∀ i : Fin 200, Compatible (407200 + i.val) →
    (table.lookup (407200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2036 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 407200 407400 :=
  FiniteIntervals.of_fin 407200 200 complete_chunk2036

lemma complete_chunk2037 : ∀ i : Fin 200, Compatible (407400 + i.val) →
    (table.lookup (407400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2037 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 407400 407600 :=
  FiniteIntervals.of_fin 407400 200 complete_chunk2037

lemma complete_chunk2038 : ∀ i : Fin 200, Compatible (407600 + i.val) →
    (table.lookup (407600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2038 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 407600 407800 :=
  FiniteIntervals.of_fin 407600 200 complete_chunk2038

lemma complete_chunk2039 : ∀ i : Fin 200, Compatible (407800 + i.val) →
    (table.lookup (407800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2039 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 407800 408000 :=
  FiniteIntervals.of_fin 407800 200 complete_chunk2039

#print axioms interval_chunk2030
end Erdos184Work.PureFiveFilter4
