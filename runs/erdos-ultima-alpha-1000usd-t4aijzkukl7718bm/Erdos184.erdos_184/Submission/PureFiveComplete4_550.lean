import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5500 : ∀ i : Fin 200, Compatible (1100000 + i.val) →
    (table.lookup (1100000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5500 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1100000 1100200 :=
  FiniteIntervals.of_fin 1100000 200 complete_chunk5500

lemma complete_chunk5501 : ∀ i : Fin 200, Compatible (1100200 + i.val) →
    (table.lookup (1100200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5501 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1100200 1100400 :=
  FiniteIntervals.of_fin 1100200 200 complete_chunk5501

lemma complete_chunk5502 : ∀ i : Fin 200, Compatible (1100400 + i.val) →
    (table.lookup (1100400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5502 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1100400 1100600 :=
  FiniteIntervals.of_fin 1100400 200 complete_chunk5502

lemma complete_chunk5503 : ∀ i : Fin 200, Compatible (1100600 + i.val) →
    (table.lookup (1100600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5503 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1100600 1100800 :=
  FiniteIntervals.of_fin 1100600 200 complete_chunk5503

lemma complete_chunk5504 : ∀ i : Fin 200, Compatible (1100800 + i.val) →
    (table.lookup (1100800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5504 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1100800 1101000 :=
  FiniteIntervals.of_fin 1100800 200 complete_chunk5504

lemma complete_chunk5505 : ∀ i : Fin 200, Compatible (1101000 + i.val) →
    (table.lookup (1101000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5505 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1101000 1101200 :=
  FiniteIntervals.of_fin 1101000 200 complete_chunk5505

lemma complete_chunk5506 : ∀ i : Fin 200, Compatible (1101200 + i.val) →
    (table.lookup (1101200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5506 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1101200 1101400 :=
  FiniteIntervals.of_fin 1101200 200 complete_chunk5506

lemma complete_chunk5507 : ∀ i : Fin 200, Compatible (1101400 + i.val) →
    (table.lookup (1101400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5507 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1101400 1101600 :=
  FiniteIntervals.of_fin 1101400 200 complete_chunk5507

lemma complete_chunk5508 : ∀ i : Fin 200, Compatible (1101600 + i.val) →
    (table.lookup (1101600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5508 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1101600 1101800 :=
  FiniteIntervals.of_fin 1101600 200 complete_chunk5508

lemma complete_chunk5509 : ∀ i : Fin 200, Compatible (1101800 + i.val) →
    (table.lookup (1101800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5509 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1101800 1102000 :=
  FiniteIntervals.of_fin 1101800 200 complete_chunk5509

#print axioms interval_chunk5500
end Erdos184Work.PureFiveFilter4
