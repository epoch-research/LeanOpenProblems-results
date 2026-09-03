import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3300 : ∀ i : Fin 200, Compatible (660000 + i.val) →
    (table.lookup (660000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3300 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 660000 660200 :=
  FiniteIntervals.of_fin 660000 200 complete_chunk3300

lemma complete_chunk3301 : ∀ i : Fin 200, Compatible (660200 + i.val) →
    (table.lookup (660200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3301 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 660200 660400 :=
  FiniteIntervals.of_fin 660200 200 complete_chunk3301

lemma complete_chunk3302 : ∀ i : Fin 200, Compatible (660400 + i.val) →
    (table.lookup (660400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3302 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 660400 660600 :=
  FiniteIntervals.of_fin 660400 200 complete_chunk3302

lemma complete_chunk3303 : ∀ i : Fin 200, Compatible (660600 + i.val) →
    (table.lookup (660600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3303 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 660600 660800 :=
  FiniteIntervals.of_fin 660600 200 complete_chunk3303

lemma complete_chunk3304 : ∀ i : Fin 200, Compatible (660800 + i.val) →
    (table.lookup (660800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3304 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 660800 661000 :=
  FiniteIntervals.of_fin 660800 200 complete_chunk3304

lemma complete_chunk3305 : ∀ i : Fin 200, Compatible (661000 + i.val) →
    (table.lookup (661000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3305 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 661000 661200 :=
  FiniteIntervals.of_fin 661000 200 complete_chunk3305

lemma complete_chunk3306 : ∀ i : Fin 200, Compatible (661200 + i.val) →
    (table.lookup (661200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3306 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 661200 661400 :=
  FiniteIntervals.of_fin 661200 200 complete_chunk3306

lemma complete_chunk3307 : ∀ i : Fin 200, Compatible (661400 + i.val) →
    (table.lookup (661400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3307 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 661400 661600 :=
  FiniteIntervals.of_fin 661400 200 complete_chunk3307

lemma complete_chunk3308 : ∀ i : Fin 200, Compatible (661600 + i.val) →
    (table.lookup (661600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3308 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 661600 661800 :=
  FiniteIntervals.of_fin 661600 200 complete_chunk3308

lemma complete_chunk3309 : ∀ i : Fin 200, Compatible (661800 + i.val) →
    (table.lookup (661800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3309 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 661800 662000 :=
  FiniteIntervals.of_fin 661800 200 complete_chunk3309

#print axioms interval_chunk3300
end Erdos184Work.PureFiveFilter4
