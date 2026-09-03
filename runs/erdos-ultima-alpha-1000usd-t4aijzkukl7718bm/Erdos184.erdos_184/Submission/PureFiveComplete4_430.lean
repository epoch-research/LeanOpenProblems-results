import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4300 : ∀ i : Fin 200, Compatible (860000 + i.val) →
    (table.lookup (860000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4300 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 860000 860200 :=
  FiniteIntervals.of_fin 860000 200 complete_chunk4300

lemma complete_chunk4301 : ∀ i : Fin 200, Compatible (860200 + i.val) →
    (table.lookup (860200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4301 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 860200 860400 :=
  FiniteIntervals.of_fin 860200 200 complete_chunk4301

lemma complete_chunk4302 : ∀ i : Fin 200, Compatible (860400 + i.val) →
    (table.lookup (860400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4302 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 860400 860600 :=
  FiniteIntervals.of_fin 860400 200 complete_chunk4302

lemma complete_chunk4303 : ∀ i : Fin 200, Compatible (860600 + i.val) →
    (table.lookup (860600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4303 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 860600 860800 :=
  FiniteIntervals.of_fin 860600 200 complete_chunk4303

lemma complete_chunk4304 : ∀ i : Fin 200, Compatible (860800 + i.val) →
    (table.lookup (860800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4304 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 860800 861000 :=
  FiniteIntervals.of_fin 860800 200 complete_chunk4304

lemma complete_chunk4305 : ∀ i : Fin 200, Compatible (861000 + i.val) →
    (table.lookup (861000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4305 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 861000 861200 :=
  FiniteIntervals.of_fin 861000 200 complete_chunk4305

lemma complete_chunk4306 : ∀ i : Fin 200, Compatible (861200 + i.val) →
    (table.lookup (861200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4306 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 861200 861400 :=
  FiniteIntervals.of_fin 861200 200 complete_chunk4306

lemma complete_chunk4307 : ∀ i : Fin 200, Compatible (861400 + i.val) →
    (table.lookup (861400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4307 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 861400 861600 :=
  FiniteIntervals.of_fin 861400 200 complete_chunk4307

lemma complete_chunk4308 : ∀ i : Fin 200, Compatible (861600 + i.val) →
    (table.lookup (861600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4308 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 861600 861800 :=
  FiniteIntervals.of_fin 861600 200 complete_chunk4308

lemma complete_chunk4309 : ∀ i : Fin 200, Compatible (861800 + i.val) →
    (table.lookup (861800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4309 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 861800 862000 :=
  FiniteIntervals.of_fin 861800 200 complete_chunk4309

#print axioms interval_chunk4300
end Erdos184Work.PureFiveFilter4
