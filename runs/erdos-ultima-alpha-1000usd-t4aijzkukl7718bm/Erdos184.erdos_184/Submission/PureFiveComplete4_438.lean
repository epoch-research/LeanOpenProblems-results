import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4380 : ∀ i : Fin 200, Compatible (876000 + i.val) →
    (table.lookup (876000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4380 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 876000 876200 :=
  FiniteIntervals.of_fin 876000 200 complete_chunk4380

lemma complete_chunk4381 : ∀ i : Fin 200, Compatible (876200 + i.val) →
    (table.lookup (876200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4381 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 876200 876400 :=
  FiniteIntervals.of_fin 876200 200 complete_chunk4381

lemma complete_chunk4382 : ∀ i : Fin 200, Compatible (876400 + i.val) →
    (table.lookup (876400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4382 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 876400 876600 :=
  FiniteIntervals.of_fin 876400 200 complete_chunk4382

lemma complete_chunk4383 : ∀ i : Fin 200, Compatible (876600 + i.val) →
    (table.lookup (876600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4383 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 876600 876800 :=
  FiniteIntervals.of_fin 876600 200 complete_chunk4383

lemma complete_chunk4384 : ∀ i : Fin 200, Compatible (876800 + i.val) →
    (table.lookup (876800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4384 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 876800 877000 :=
  FiniteIntervals.of_fin 876800 200 complete_chunk4384

lemma complete_chunk4385 : ∀ i : Fin 200, Compatible (877000 + i.val) →
    (table.lookup (877000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4385 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 877000 877200 :=
  FiniteIntervals.of_fin 877000 200 complete_chunk4385

lemma complete_chunk4386 : ∀ i : Fin 200, Compatible (877200 + i.val) →
    (table.lookup (877200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4386 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 877200 877400 :=
  FiniteIntervals.of_fin 877200 200 complete_chunk4386

lemma complete_chunk4387 : ∀ i : Fin 200, Compatible (877400 + i.val) →
    (table.lookup (877400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4387 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 877400 877600 :=
  FiniteIntervals.of_fin 877400 200 complete_chunk4387

lemma complete_chunk4388 : ∀ i : Fin 200, Compatible (877600 + i.val) →
    (table.lookup (877600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4388 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 877600 877800 :=
  FiniteIntervals.of_fin 877600 200 complete_chunk4388

lemma complete_chunk4389 : ∀ i : Fin 200, Compatible (877800 + i.val) →
    (table.lookup (877800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4389 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 877800 878000 :=
  FiniteIntervals.of_fin 877800 200 complete_chunk4389

#print axioms interval_chunk4380
end Erdos184Work.PureFiveFilter4
