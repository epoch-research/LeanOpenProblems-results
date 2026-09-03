import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6060 : ∀ i : Fin 200, Compatible (1212000 + i.val) →
    (table.lookup (1212000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6060 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1212000 1212200 :=
  FiniteIntervals.of_fin 1212000 200 complete_chunk6060

lemma complete_chunk6061 : ∀ i : Fin 200, Compatible (1212200 + i.val) →
    (table.lookup (1212200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6061 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1212200 1212400 :=
  FiniteIntervals.of_fin 1212200 200 complete_chunk6061

lemma complete_chunk6062 : ∀ i : Fin 200, Compatible (1212400 + i.val) →
    (table.lookup (1212400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6062 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1212400 1212600 :=
  FiniteIntervals.of_fin 1212400 200 complete_chunk6062

lemma complete_chunk6063 : ∀ i : Fin 200, Compatible (1212600 + i.val) →
    (table.lookup (1212600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6063 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1212600 1212800 :=
  FiniteIntervals.of_fin 1212600 200 complete_chunk6063

lemma complete_chunk6064 : ∀ i : Fin 200, Compatible (1212800 + i.val) →
    (table.lookup (1212800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6064 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1212800 1213000 :=
  FiniteIntervals.of_fin 1212800 200 complete_chunk6064

lemma complete_chunk6065 : ∀ i : Fin 200, Compatible (1213000 + i.val) →
    (table.lookup (1213000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6065 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1213000 1213200 :=
  FiniteIntervals.of_fin 1213000 200 complete_chunk6065

lemma complete_chunk6066 : ∀ i : Fin 200, Compatible (1213200 + i.val) →
    (table.lookup (1213200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6066 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1213200 1213400 :=
  FiniteIntervals.of_fin 1213200 200 complete_chunk6066

lemma complete_chunk6067 : ∀ i : Fin 200, Compatible (1213400 + i.val) →
    (table.lookup (1213400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6067 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1213400 1213600 :=
  FiniteIntervals.of_fin 1213400 200 complete_chunk6067

lemma complete_chunk6068 : ∀ i : Fin 200, Compatible (1213600 + i.val) →
    (table.lookup (1213600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6068 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1213600 1213800 :=
  FiniteIntervals.of_fin 1213600 200 complete_chunk6068

lemma complete_chunk6069 : ∀ i : Fin 200, Compatible (1213800 + i.val) →
    (table.lookup (1213800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6069 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1213800 1214000 :=
  FiniteIntervals.of_fin 1213800 200 complete_chunk6069

#print axioms interval_chunk6060
end Erdos184Work.PureFiveFilter4
