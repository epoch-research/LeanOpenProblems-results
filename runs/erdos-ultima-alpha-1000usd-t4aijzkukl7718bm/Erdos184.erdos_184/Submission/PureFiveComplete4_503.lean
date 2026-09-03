import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5030 : ∀ i : Fin 200, Compatible (1006000 + i.val) →
    (table.lookup (1006000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5030 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1006000 1006200 :=
  FiniteIntervals.of_fin 1006000 200 complete_chunk5030

lemma complete_chunk5031 : ∀ i : Fin 200, Compatible (1006200 + i.val) →
    (table.lookup (1006200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5031 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1006200 1006400 :=
  FiniteIntervals.of_fin 1006200 200 complete_chunk5031

lemma complete_chunk5032 : ∀ i : Fin 200, Compatible (1006400 + i.val) →
    (table.lookup (1006400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5032 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1006400 1006600 :=
  FiniteIntervals.of_fin 1006400 200 complete_chunk5032

lemma complete_chunk5033 : ∀ i : Fin 200, Compatible (1006600 + i.val) →
    (table.lookup (1006600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5033 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1006600 1006800 :=
  FiniteIntervals.of_fin 1006600 200 complete_chunk5033

lemma complete_chunk5034 : ∀ i : Fin 200, Compatible (1006800 + i.val) →
    (table.lookup (1006800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5034 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1006800 1007000 :=
  FiniteIntervals.of_fin 1006800 200 complete_chunk5034

lemma complete_chunk5035 : ∀ i : Fin 200, Compatible (1007000 + i.val) →
    (table.lookup (1007000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5035 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1007000 1007200 :=
  FiniteIntervals.of_fin 1007000 200 complete_chunk5035

lemma complete_chunk5036 : ∀ i : Fin 200, Compatible (1007200 + i.val) →
    (table.lookup (1007200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5036 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1007200 1007400 :=
  FiniteIntervals.of_fin 1007200 200 complete_chunk5036

lemma complete_chunk5037 : ∀ i : Fin 200, Compatible (1007400 + i.val) →
    (table.lookup (1007400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5037 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1007400 1007600 :=
  FiniteIntervals.of_fin 1007400 200 complete_chunk5037

lemma complete_chunk5038 : ∀ i : Fin 200, Compatible (1007600 + i.val) →
    (table.lookup (1007600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5038 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1007600 1007800 :=
  FiniteIntervals.of_fin 1007600 200 complete_chunk5038

lemma complete_chunk5039 : ∀ i : Fin 200, Compatible (1007800 + i.val) →
    (table.lookup (1007800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5039 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1007800 1008000 :=
  FiniteIntervals.of_fin 1007800 200 complete_chunk5039

#print axioms interval_chunk5030
end Erdos184Work.PureFiveFilter4
