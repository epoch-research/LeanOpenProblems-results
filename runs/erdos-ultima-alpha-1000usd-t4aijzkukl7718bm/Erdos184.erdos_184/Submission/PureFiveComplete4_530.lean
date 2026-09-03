import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5300 : ∀ i : Fin 200, Compatible (1060000 + i.val) →
    (table.lookup (1060000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5300 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1060000 1060200 :=
  FiniteIntervals.of_fin 1060000 200 complete_chunk5300

lemma complete_chunk5301 : ∀ i : Fin 200, Compatible (1060200 + i.val) →
    (table.lookup (1060200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5301 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1060200 1060400 :=
  FiniteIntervals.of_fin 1060200 200 complete_chunk5301

lemma complete_chunk5302 : ∀ i : Fin 200, Compatible (1060400 + i.val) →
    (table.lookup (1060400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5302 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1060400 1060600 :=
  FiniteIntervals.of_fin 1060400 200 complete_chunk5302

lemma complete_chunk5303 : ∀ i : Fin 200, Compatible (1060600 + i.val) →
    (table.lookup (1060600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5303 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1060600 1060800 :=
  FiniteIntervals.of_fin 1060600 200 complete_chunk5303

lemma complete_chunk5304 : ∀ i : Fin 200, Compatible (1060800 + i.val) →
    (table.lookup (1060800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5304 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1060800 1061000 :=
  FiniteIntervals.of_fin 1060800 200 complete_chunk5304

lemma complete_chunk5305 : ∀ i : Fin 200, Compatible (1061000 + i.val) →
    (table.lookup (1061000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5305 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1061000 1061200 :=
  FiniteIntervals.of_fin 1061000 200 complete_chunk5305

lemma complete_chunk5306 : ∀ i : Fin 200, Compatible (1061200 + i.val) →
    (table.lookup (1061200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5306 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1061200 1061400 :=
  FiniteIntervals.of_fin 1061200 200 complete_chunk5306

lemma complete_chunk5307 : ∀ i : Fin 200, Compatible (1061400 + i.val) →
    (table.lookup (1061400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5307 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1061400 1061600 :=
  FiniteIntervals.of_fin 1061400 200 complete_chunk5307

lemma complete_chunk5308 : ∀ i : Fin 200, Compatible (1061600 + i.val) →
    (table.lookup (1061600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5308 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1061600 1061800 :=
  FiniteIntervals.of_fin 1061600 200 complete_chunk5308

lemma complete_chunk5309 : ∀ i : Fin 200, Compatible (1061800 + i.val) →
    (table.lookup (1061800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5309 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1061800 1062000 :=
  FiniteIntervals.of_fin 1061800 200 complete_chunk5309

#print axioms interval_chunk5300
end Erdos184Work.PureFiveFilter4
