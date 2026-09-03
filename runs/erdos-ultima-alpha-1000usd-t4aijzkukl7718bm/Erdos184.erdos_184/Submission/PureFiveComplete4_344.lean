import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3440 : ∀ i : Fin 200, Compatible (688000 + i.val) →
    (table.lookup (688000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3440 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 688000 688200 :=
  FiniteIntervals.of_fin 688000 200 complete_chunk3440

lemma complete_chunk3441 : ∀ i : Fin 200, Compatible (688200 + i.val) →
    (table.lookup (688200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3441 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 688200 688400 :=
  FiniteIntervals.of_fin 688200 200 complete_chunk3441

lemma complete_chunk3442 : ∀ i : Fin 200, Compatible (688400 + i.val) →
    (table.lookup (688400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3442 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 688400 688600 :=
  FiniteIntervals.of_fin 688400 200 complete_chunk3442

lemma complete_chunk3443 : ∀ i : Fin 200, Compatible (688600 + i.val) →
    (table.lookup (688600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3443 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 688600 688800 :=
  FiniteIntervals.of_fin 688600 200 complete_chunk3443

lemma complete_chunk3444 : ∀ i : Fin 200, Compatible (688800 + i.val) →
    (table.lookup (688800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3444 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 688800 689000 :=
  FiniteIntervals.of_fin 688800 200 complete_chunk3444

lemma complete_chunk3445 : ∀ i : Fin 200, Compatible (689000 + i.val) →
    (table.lookup (689000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3445 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 689000 689200 :=
  FiniteIntervals.of_fin 689000 200 complete_chunk3445

lemma complete_chunk3446 : ∀ i : Fin 200, Compatible (689200 + i.val) →
    (table.lookup (689200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3446 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 689200 689400 :=
  FiniteIntervals.of_fin 689200 200 complete_chunk3446

lemma complete_chunk3447 : ∀ i : Fin 200, Compatible (689400 + i.val) →
    (table.lookup (689400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3447 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 689400 689600 :=
  FiniteIntervals.of_fin 689400 200 complete_chunk3447

lemma complete_chunk3448 : ∀ i : Fin 200, Compatible (689600 + i.val) →
    (table.lookup (689600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3448 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 689600 689800 :=
  FiniteIntervals.of_fin 689600 200 complete_chunk3448

lemma complete_chunk3449 : ∀ i : Fin 200, Compatible (689800 + i.val) →
    (table.lookup (689800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3449 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 689800 690000 :=
  FiniteIntervals.of_fin 689800 200 complete_chunk3449

#print axioms interval_chunk3440
end Erdos184Work.PureFiveFilter4
