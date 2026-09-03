import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3000 : ∀ i : Fin 200, Compatible (600000 + i.val) →
    (table.lookup (600000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3000 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 600000 600200 :=
  FiniteIntervals.of_fin 600000 200 complete_chunk3000

lemma complete_chunk3001 : ∀ i : Fin 200, Compatible (600200 + i.val) →
    (table.lookup (600200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3001 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 600200 600400 :=
  FiniteIntervals.of_fin 600200 200 complete_chunk3001

lemma complete_chunk3002 : ∀ i : Fin 200, Compatible (600400 + i.val) →
    (table.lookup (600400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3002 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 600400 600600 :=
  FiniteIntervals.of_fin 600400 200 complete_chunk3002

lemma complete_chunk3003 : ∀ i : Fin 200, Compatible (600600 + i.val) →
    (table.lookup (600600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3003 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 600600 600800 :=
  FiniteIntervals.of_fin 600600 200 complete_chunk3003

lemma complete_chunk3004 : ∀ i : Fin 200, Compatible (600800 + i.val) →
    (table.lookup (600800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3004 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 600800 601000 :=
  FiniteIntervals.of_fin 600800 200 complete_chunk3004

lemma complete_chunk3005 : ∀ i : Fin 200, Compatible (601000 + i.val) →
    (table.lookup (601000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3005 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 601000 601200 :=
  FiniteIntervals.of_fin 601000 200 complete_chunk3005

lemma complete_chunk3006 : ∀ i : Fin 200, Compatible (601200 + i.val) →
    (table.lookup (601200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3006 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 601200 601400 :=
  FiniteIntervals.of_fin 601200 200 complete_chunk3006

lemma complete_chunk3007 : ∀ i : Fin 200, Compatible (601400 + i.val) →
    (table.lookup (601400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3007 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 601400 601600 :=
  FiniteIntervals.of_fin 601400 200 complete_chunk3007

lemma complete_chunk3008 : ∀ i : Fin 200, Compatible (601600 + i.val) →
    (table.lookup (601600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3008 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 601600 601800 :=
  FiniteIntervals.of_fin 601600 200 complete_chunk3008

lemma complete_chunk3009 : ∀ i : Fin 200, Compatible (601800 + i.val) →
    (table.lookup (601800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3009 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 601800 602000 :=
  FiniteIntervals.of_fin 601800 200 complete_chunk3009

#print axioms interval_chunk3000
end Erdos184Work.PureFiveFilter4
