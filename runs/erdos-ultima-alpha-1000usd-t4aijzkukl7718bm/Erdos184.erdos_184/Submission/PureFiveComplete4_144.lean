import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1440 : ∀ i : Fin 200, Compatible (288000 + i.val) →
    (table.lookup (288000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1440 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 288000 288200 :=
  FiniteIntervals.of_fin 288000 200 complete_chunk1440

lemma complete_chunk1441 : ∀ i : Fin 200, Compatible (288200 + i.val) →
    (table.lookup (288200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1441 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 288200 288400 :=
  FiniteIntervals.of_fin 288200 200 complete_chunk1441

lemma complete_chunk1442 : ∀ i : Fin 200, Compatible (288400 + i.val) →
    (table.lookup (288400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1442 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 288400 288600 :=
  FiniteIntervals.of_fin 288400 200 complete_chunk1442

lemma complete_chunk1443 : ∀ i : Fin 200, Compatible (288600 + i.val) →
    (table.lookup (288600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1443 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 288600 288800 :=
  FiniteIntervals.of_fin 288600 200 complete_chunk1443

lemma complete_chunk1444 : ∀ i : Fin 200, Compatible (288800 + i.val) →
    (table.lookup (288800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1444 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 288800 289000 :=
  FiniteIntervals.of_fin 288800 200 complete_chunk1444

lemma complete_chunk1445 : ∀ i : Fin 200, Compatible (289000 + i.val) →
    (table.lookup (289000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1445 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 289000 289200 :=
  FiniteIntervals.of_fin 289000 200 complete_chunk1445

lemma complete_chunk1446 : ∀ i : Fin 200, Compatible (289200 + i.val) →
    (table.lookup (289200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1446 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 289200 289400 :=
  FiniteIntervals.of_fin 289200 200 complete_chunk1446

lemma complete_chunk1447 : ∀ i : Fin 200, Compatible (289400 + i.val) →
    (table.lookup (289400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1447 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 289400 289600 :=
  FiniteIntervals.of_fin 289400 200 complete_chunk1447

lemma complete_chunk1448 : ∀ i : Fin 200, Compatible (289600 + i.val) →
    (table.lookup (289600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1448 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 289600 289800 :=
  FiniteIntervals.of_fin 289600 200 complete_chunk1448

lemma complete_chunk1449 : ∀ i : Fin 200, Compatible (289800 + i.val) →
    (table.lookup (289800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1449 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 289800 290000 :=
  FiniteIntervals.of_fin 289800 200 complete_chunk1449

#print axioms interval_chunk1440
end Erdos184Work.PureFiveFilter4
