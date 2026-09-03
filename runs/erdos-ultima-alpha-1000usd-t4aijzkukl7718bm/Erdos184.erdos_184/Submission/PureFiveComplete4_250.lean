import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2500 : ∀ i : Fin 200, Compatible (500000 + i.val) →
    (table.lookup (500000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2500 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 500000 500200 :=
  FiniteIntervals.of_fin 500000 200 complete_chunk2500

lemma complete_chunk2501 : ∀ i : Fin 200, Compatible (500200 + i.val) →
    (table.lookup (500200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2501 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 500200 500400 :=
  FiniteIntervals.of_fin 500200 200 complete_chunk2501

lemma complete_chunk2502 : ∀ i : Fin 200, Compatible (500400 + i.val) →
    (table.lookup (500400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2502 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 500400 500600 :=
  FiniteIntervals.of_fin 500400 200 complete_chunk2502

lemma complete_chunk2503 : ∀ i : Fin 200, Compatible (500600 + i.val) →
    (table.lookup (500600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2503 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 500600 500800 :=
  FiniteIntervals.of_fin 500600 200 complete_chunk2503

lemma complete_chunk2504 : ∀ i : Fin 200, Compatible (500800 + i.val) →
    (table.lookup (500800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2504 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 500800 501000 :=
  FiniteIntervals.of_fin 500800 200 complete_chunk2504

lemma complete_chunk2505 : ∀ i : Fin 200, Compatible (501000 + i.val) →
    (table.lookup (501000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2505 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 501000 501200 :=
  FiniteIntervals.of_fin 501000 200 complete_chunk2505

lemma complete_chunk2506 : ∀ i : Fin 200, Compatible (501200 + i.val) →
    (table.lookup (501200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2506 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 501200 501400 :=
  FiniteIntervals.of_fin 501200 200 complete_chunk2506

lemma complete_chunk2507 : ∀ i : Fin 200, Compatible (501400 + i.val) →
    (table.lookup (501400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2507 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 501400 501600 :=
  FiniteIntervals.of_fin 501400 200 complete_chunk2507

lemma complete_chunk2508 : ∀ i : Fin 200, Compatible (501600 + i.val) →
    (table.lookup (501600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2508 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 501600 501800 :=
  FiniteIntervals.of_fin 501600 200 complete_chunk2508

lemma complete_chunk2509 : ∀ i : Fin 200, Compatible (501800 + i.val) →
    (table.lookup (501800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2509 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 501800 502000 :=
  FiniteIntervals.of_fin 501800 200 complete_chunk2509

#print axioms interval_chunk2500
end Erdos184Work.PureFiveFilter4
