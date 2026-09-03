import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3970 : ∀ i : Fin 200, Compatible (794000 + i.val) →
    (table.lookup (794000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3970 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 794000 794200 :=
  FiniteIntervals.of_fin 794000 200 complete_chunk3970

lemma complete_chunk3971 : ∀ i : Fin 200, Compatible (794200 + i.val) →
    (table.lookup (794200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3971 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 794200 794400 :=
  FiniteIntervals.of_fin 794200 200 complete_chunk3971

lemma complete_chunk3972 : ∀ i : Fin 200, Compatible (794400 + i.val) →
    (table.lookup (794400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3972 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 794400 794600 :=
  FiniteIntervals.of_fin 794400 200 complete_chunk3972

lemma complete_chunk3973 : ∀ i : Fin 200, Compatible (794600 + i.val) →
    (table.lookup (794600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3973 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 794600 794800 :=
  FiniteIntervals.of_fin 794600 200 complete_chunk3973

lemma complete_chunk3974 : ∀ i : Fin 200, Compatible (794800 + i.val) →
    (table.lookup (794800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3974 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 794800 795000 :=
  FiniteIntervals.of_fin 794800 200 complete_chunk3974

lemma complete_chunk3975 : ∀ i : Fin 200, Compatible (795000 + i.val) →
    (table.lookup (795000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3975 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 795000 795200 :=
  FiniteIntervals.of_fin 795000 200 complete_chunk3975

lemma complete_chunk3976 : ∀ i : Fin 200, Compatible (795200 + i.val) →
    (table.lookup (795200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3976 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 795200 795400 :=
  FiniteIntervals.of_fin 795200 200 complete_chunk3976

lemma complete_chunk3977 : ∀ i : Fin 200, Compatible (795400 + i.val) →
    (table.lookup (795400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3977 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 795400 795600 :=
  FiniteIntervals.of_fin 795400 200 complete_chunk3977

lemma complete_chunk3978 : ∀ i : Fin 200, Compatible (795600 + i.val) →
    (table.lookup (795600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3978 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 795600 795800 :=
  FiniteIntervals.of_fin 795600 200 complete_chunk3978

lemma complete_chunk3979 : ∀ i : Fin 200, Compatible (795800 + i.val) →
    (table.lookup (795800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3979 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 795800 796000 :=
  FiniteIntervals.of_fin 795800 200 complete_chunk3979

#print axioms interval_chunk3970
end Erdos184Work.PureFiveFilter4
